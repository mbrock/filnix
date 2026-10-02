# Campaign analytics object store

The campaign publisher reads SQLite and captured attempt logs without changing
the coordinator. It writes Zstandard-compressed Parquet to a private S3 bucket
in Frankfurt (`eu-central-1`). SQLite remains authoritative; AWS outages do not
block builds. The dashboard still reads SQLite, pending a separate parity and
query-performance assessment. S3 storage, requests, and downloads are billable.

The deployed AWS foundation is in account `241036177239`:

- Bucket: `filnix-campaign-9346da1ee45ae659f7c14b4971`.
- Dataset: `s3://filnix-campaign-9346da1ee45ae659f7c14b4971/campaign/v1/`.
- Publisher: `filnix-campaign-publisher`, with access to this bucket only, and no
  object deletion or bucket administration permission.
- Canonical prefix private; an optional unlisted share prefix allows anonymous
  downloads only. ACLs disabled, encryption, versioning, TLS-only policy,
  seven-day incomplete-upload cleanup, and infrastructure destruction protection.

No Athena, Glue, EC2, customer-managed KMS key, source-log deletion,
or offline storage tier is needed.

## Bootstrap without exchanging access keys

Use AWS CLI >= 2.32 on swa. In your own SSH terminal, run:

```sh
/home/mbrock/filnix/.amp/in/aws-cli/bin/aws login --remote \
  --profile filnix-bootstrap --region eu-central-1
```

Open its URL in your browser, use a non-root IAM/federated identity with the
necessary S3/IAM provisioning permissions, and paste the authorization code into
the SSH terminal, **not into chat**. The identity also needs AWS's managed
`SignInLocalDevelopmentAccess` policy. IAM Identity Center uses `aws configure
sso` / `aws sso login` instead; do not substitute a root access key.

The CLI caches temporary credentials in `~/.aws/login/cache`. Its session lasts
up to 12 hours; this is a bootstrap session, not an unattended exporter identity.
For tools that do not yet understand `login_session`, configure a process profile
whose `credential_process` is the absolute AWS CLI executable followed by
`configure export-credentials --profile filnix-bootstrap --format process`.
Use profile name `filnix-bootstrap-tools`, with the same region. Do not run
`export-credentials` in a way that prints credentials into a transcript.

## Infrastructure state and review

Keep local state outside the checkout and private. Before initializing:

```sh
umask 077
mkdir -p "$HOME/.local/state/filnix-analytics"
tofu init -backend-config="path=$HOME/.local/state/filnix-analytics/terraform.tfstate"
tofu validate
tofu plan
```

Run these from `deploy/analytics`. Inspect the account, resources and costs before
applying; no existing bucket or IAM user should be silently adopted. The bucket
has encryption, versioning, scoped access controls, TLS-only access, automatic
abortion of seven-day-old incomplete uploads, and destruction protection.
Objects do not expire or move into an offline retrieval tier. Publisher access
does not include object deletion, bucket administration or any other bucket.

The machine access key is installed root-owned, mode 0600 at
`/etc/filnix-analytics/aws-credentials`. It was created outside Terraform, so its
secret is neither in infrastructure state nor Git. systemd passes it through
`LoadCredential`, not command arguments or plaintext environment values. The
unattended publisher does not depend on the twelve-hour browser login. Rotate
this key through IAM, installing the replacement privately before retiring the
old key. Do not put credentials, captured logs or infrastructure state into Git.

Preserve the private state at `~/.local/state/filnix-analytics/terraform.tfstate`.
Losing it does not delete the bucket, but requires deliberate resource import
before managing the same infrastructure again.

## Publishing and recovery

Build and install the standalone native-Python publisher without replacing the
controller or dashboard application:

```sh
nix build -f deploy/analytics/default.nix -o result-analytics
sudo deploy/analytics/install "$(readlink -f result-analytics)" \
  filnix-campaign-9346da1ee45ae659f7c14b4971
sudo systemctl start filnix-analytics.service
# After verifying the first generation:
sudo systemctl enable --now filnix-analytics.timer
```

The timer refreshes fifteen minutes after a run completes; it never overlaps
runs. The service is low CPU/I/O priority, limited to two CPUs and 3 GiB RAM.
There is up to one minute of jitter. A five-minute run therefore starts roughly
every twenty minutes, not every fifteen minutes on the clock. The interval is
an operator-selected load/freshness tradeoff, not an S3 or DuckDB requirement.
Its configuration is `/etc/filnix-analytics/config.json`. Default log catch-up
budget is 1 GiB per run; Arrow batches are bounded by rows and approximately
8 MiB of source payload (a single larger row is kept intact). Staging stops if
free disk reaches the configured 20 GiB reserve. The publisher's own hash index,
pending upload journal and spools live in private `/var/lib/filnix-analytics`.

For bulk catch-up, `--log-bytes 34359738368` overrides the byte budget for one
run (32 GiB) without changing the persistent configuration. Pause the timer,
let any current service finish, then run with the same systemd credentials and
resource protections using a temporary runtime `ExecStart` override. Remove
that override and resume the timer afterwards. A large budget changes staging
and transfer volume, not the in-memory batch bounds or crash-recovery protocol.
If there is a pending generation, it finishes unchanged before the new budget
can take effect in the next generation.

This first version rescans mutable tables locally to detect changes/deletions;
the source does not provide a complete change journal. It uploads only changes,
not a rewritten database snapshot. Events resume by sequence, logs by byte
offset. Long-lived source read transactions can temporarily delay SQLite WAL
checkpointing; inspect runtime and WAL growth when tuning the refresh interval.

- Append-only campaign events: ordered by `events.seq`.
- Build logs: Parquet records contain the exact raw bytes as `BLOB`, alongside
  searchable text and the original attempt, stream, `[start,end)` byte range,
  Nix activity ID and derivation when known. Records are newline-aware, with
  bounded fragments for oversized/budget-split lines. Malformed UTF-8 and torn
  terminal lines survive in `raw`; decoded `text` is deliberately lossy. Live
  stderr never exceeds the controller's committed offset. Source capture is
  already capped and filtered; the original omission/truncation metadata stays
  in `attempts.result`. Planner graph scratch and Nix store outputs are not logs
  and are not exported.
- Mutable tables (attempts, activities, package state, derivation metadata,
  dependencies and classifications): versioned snapshot observations, not a
  falsely advertised complete change-data-capture stream. Historical log/event
  segments must not be rewritten on every refresh.
- A durable local pending journal is written before uploads. On restart it must
  finish the same generation before consuming further source data. Referenced
  objects and the immutable generation manifest are uploaded before conditional
  publication of `latest.json`; only then is the row hash index finalized and
  the spool discarded. Failures before/after pointer publication are retryable.
  Different destinations, unexpected parents, lost remote pointers and rewound
  event cursors are rejected, not silently overwritten. Never delete the local
  checkpoint to "fix" an upload failure: it belongs to this dataset.

Each manifest contains source schema/primary keys, snapshot time, event
watermark and explicit delta object keys. Objects are partitioned by table and,
for logs, attempt/stream. Readers pin `latest.json`, then follow `parent` to the
initial generation. Prefix globbing could accidentally include uncommitted
uploads and is not the supported read protocol. Backfilling old logs takes
multiple runs; successful publication of metadata does not imply all historic
logs are already archived. Published generations do not expire automatically.

Monitor with `systemctl status filnix-analytics.{service,timer}` and
`journalctl -u filnix-analytics.service`. A successful oneshot is normally
inactive/dead with result `success`; the timer remains active. Failed uploads
leave the pending spool intact for retry. No original logs are removed by this
service, even after upload.

## DuckDB exploration

The reader pins the manifest chain and creates typed views named after all
twelve source tables, plus `temporal_<table>` observations and `build_logs`.
Latest views choose the greatest `_revision` per primary key and apply
tombstones **after** choosing it. `_observed_at` is the consistent snapshot
observation time, not an inferred source mutation time. Empty source tables
remain queryable. Earlier history before the first export cannot be recreated
except for existing source events/logs.

On swa, with your browser/process profile authenticated:

```sh
AWS_PROFILE=filnix-bootstrap-tools /opt/filnix-analytics/bin/filnix-analytics \
  --config /etc/filnix-analytics/config.json \
  --query 'SELECT state, count(*) FROM candidates GROUP BY state'

AWS_PROFILE=filnix-bootstrap-tools /opt/filnix-analytics/bin/filnix-analytics \
  --config /etc/filnix-analytics/config.json \
  --query 'SELECT c.label, d.name, d.failure FROM candidates c
           JOIN derivations d ON c.drv=d.drv WHERE d.failure IS NOT NULL LIMIT 20'
```

The native Python environment includes DuckDB. Install/load its official
`httpfs` and `aws` extensions once per reader machine if not cached. The helper
uses DuckDB's AWS credential chain and your selected `AWS_PROFILE`; it never
embeds keys in generated SQL. For the browser-login compatibility profile,
the equivalent interactive secret is:

```sql
INSTALL httpfs; LOAD httpfs;
INSTALL aws; LOAD aws;
CREATE SECRET (TYPE s3, PROVIDER credential_chain,
  CHAIN 'process', PROFILE 'filnix-bootstrap-tools', REGION 'eu-central-1');
```

From another machine, authenticate a reader there; a signed URL only authorizes
one object for a limited time and is not a durable dataset credential. Readers
need `s3:GetObject` for this prefix; no write/admin access is required. Use
`experiment.analytics.load_chain` and `latest_sql` to generate the same views
in your own DuckDB session. Log filters on `attempt`/`stream` can prune the hive
partitions; joining `build_logs.derivation` to `derivations.drv` associates output
with build metadata. Reconstruct raw streams by concatenating `raw` ordered by
`start`, checking contiguous ranges, not by concatenating decoded text.

Raw log offsets give ordering, not wall-clock timestamps for every line. Join
observed start/stop times from `build_times` when known; do not fabricate times
for older log lines. DuckDB can query the private Parquet data from any machine
with reader credentials. Keep the current dashboard on SQLite until schema,
refresh costs and parity are validated; switching it is a separate step.

## Public sharing and scaling

Parquet does not require a private bucket. The canonical archive includes
unfiltered attempt specs, operational policies, free-form evidence and exact
logs. A read-only audit of all twelve tables and 13.8 GiB of
captured logs on 2026-10-02 found no confirmed credentials in its tested pattern
families; three log matches were compiler/test text. This is reassuring, not a
guarantee about unknown credential formats or future output.

The operator has chosen an **unlisted full-data share**, including exact logs,
rather than a redacted research projection. This is intentional publication,
not authentication: anyone with the URL can copy the data and redistribute it.
Future exported logs/evidence are shared automatically too. Store paths and
package names are useful research identifiers, not automatically secrets.

The canonical `campaign/v1` prefix remains private. Anonymous access grants only
`s3:GetObject` under `share/<code>/v1/`; there is no anonymous bucket listing,
write permission or account-wide public-access change. The code has sixteen
lowercase base32 characters (80 random bits). No link is committed to Git or
printed by the service. A known link exposes its complete manifest inventory,
necessarily, so readers can discover/query the dataset files. Do not post it
publicly if you want to avoid discovery by crawlers. This cannot prevent
scraping or download costs once the URL is shared.

The private locator configuration is root-owned mode 0600 at
`/etc/filnix-analytics/share.json`, passed through systemd `LoadCredential`.
The private infrastructure variable file is
`~/.local/state/filnix-analytics/share.tfvars.json`. Include that file with
`tofu plan -var-file=...` when maintaining infrastructure; omitting it defaults
to disabling anonymous sharing. Terraform state/plans also contain the prefix
and must stay private. Removing the anonymous policy revokes origin access,
but cannot retract downloaded or cached copies.

`filnix-analytics-share.service` runs after successful private exports. It pins
the committed source chain, copies only newly referenced immutable objects
**server-side within S3**, and publishes a flattened inventory plus generated
DuckDB SQL. Eight copy workers and batches of at most 64 tasks bound concurrency;
there is no log download or recompression. Its final conditional `index.json`
update references immutable manifest/SQL objects only after copies succeed.
Partial copies are verified/reused after failure; the previous index stays valid.
No-change runs skip copies entirely. Sharing duplicates compressed storage and
incurs S3 copy/request charges; it does not double local staging disk.

The index URL is saved locally in `.amp/in/artifacts/analytics-share-link.txt`
(mode 0600, ignored by Git). Copy that URL to another machine and set
`FILNIX_DATASET_URL` to it. With Python's `duckdb` package installed, no AWS
credentials are required:

```python
import json, os, urllib.request
from urllib.parse import urlsplit
import duckdb

url = os.environ['FILNIX_DATASET_URL']
index = json.load(urllib.request.urlopen(url))
parsed = urlsplit(url)
origin = f'{parsed.scheme}://{parsed.netloc}'
sql = urllib.request.urlopen(origin + '/' + index['sql']).read().decode()
db = duckdb.connect()
db.execute('INSTALL httpfs; LOAD httpfs;')
db.execute(sql)
db.sql('SELECT state, count(*) FROM candidates GROUP BY state').show()
```

Pin the index once per analysis for a coherent dataset. Its `archived_log_bytes`
is cumulative; the underlying manifest's `log_bytes` retains the source
generation's delta count. The public inventory removes reader-side manifest
chain traversal, but is not Parquet compaction and retains temporal observations.

Direct HTTPS/S3 Parquet queries already work; a CDN is optional, not required.
Shared Parquet objects have year-long immutable cache headers; the current
index requires revalidation. If traffic warrants CloudFront later, a CDN
does not sanitize data or eliminate query-side metadata work.

Current scaling limits are local full-table hashing, many small per-attempt
log objects, and a manifest chain whose read cost grows with generations.
Before using this as the dashboard query backend, measure those costs and add
a checkpointed file inventory/compaction or a source-side change journal where
needed. The first implementation prioritizes source isolation and recoverable
publication over a claim of optimal CDC or warehouse performance.
