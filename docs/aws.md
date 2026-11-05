# The public AMI and its AWS account

filnix publishes its base Fil-C NixOS ([nixos/amazon.nix](../nixos/amazon.nix),
the EC2 variant of [nixos/base.nix](../nixos/base.nix)) as a public AMI in
eu-central-1. [.github/workflows/ami.yml](../.github/workflows/ami.yml) does
it, and [release.yml](../.github/workflows/release.yml) calls it for each
`v*` tag after the release is published. Nothing here is secret: the
workflow has no long-lived credentials, only a role it assumes through
GitHub's OIDC provider.

## What the workflow does

1. Substitutes `packages.x86_64-linux.nixos-ami`, a VHD the campaign built
   and cached (it is in `scripts/ci-outputs.txt`). It never builds it.
2. Uploads it to the import bucket.
3. Starts `ec2 import-snapshot` with the `vmimport` service role and polls
   it, usually for 10 to 30 minutes. It tags the snapshot `project=filnix`.
4. Registers the image: x86_64, HVM, `legacy-bios` boot (GRUB on a GPT
   disk), ENA, IMDSv2 only, a gp3 root volume. Tagged `project=filnix` at
   creation.
5. Makes it public (`launch-permission Group=all`).
6. Deregisters this project's images beyond the newest 3, and deletes their
   snapshots.
7. Deletes the upload.
8. For a `v*` tag, appends the AMI ID to the release notes.

To try a commit without a release:

```sh
git tag ami-test-1 COMMIT && git push origin ami-test-1
gh workflow run ami.yml --ref ami-test-1 -f tag=ami-test-1
# afterwards
git push origin :ami-test-1 && git tag -d ami-test-1
```

A test AMI counts toward the newest 3 like any other.

On the instance, root logs in with the instance's key pair (from the
instance metadata, `PermitRootLogin prohibit-password`), and the EC2 serial
console logs `demo` in. Give it 2 GiB of memory or more (t3.small). The
SSM agent is off (it is Go), and so is `amazon-init`, which would replace
`/etc/nixos/configuration.nix` with the user data; the machine's
configuration is the pinned flake in `/etc/nixos`.

## The account

Account 241036177239, region eu-central-1. It is the owner's general
account and has unrelated older projects, so everything filnix may change
is marked with the tag `project=filnix`.

| Resource | Setup |
| --- | --- |
| S3 bucket `filnix-ami-import-241036177239` | public access blocked; objects expire after 7 days |
| IAM role `vmimport` | trusts `vmie.amazonaws.com`; may read that bucket. `import-snapshot --role-name vmimport` |
| OIDC provider | `token.actions.githubusercontent.com` |
| IAM role `filnix-release-ami` | trusts only `repo:mbrock/filnix:environment:aws-ami`; 2-hour sessions |
| EC2 image block public access | off in eu-central-1, so public AMIs are allowed there |
| GitHub environment `aws-ami` | variables `AWS_REGION`, `AWS_ROLE_ARN`, `AMI_BUCKET`; deployments only from tags `v*` and `ami-test-*` |

`filnix-release-ami` may:

- put, get, delete and list objects in the import bucket, and nothing else in S3;
- `ImportSnapshot`, `DescribeImportSnapshotTasks`, `DescribeSnapshots`,
  `RegisterImage`, `DescribeImages`, `DescribeImageAttribute`, `CopyImage`,
  `CreateTags`, `DescribeRegions`;
- `iam:PassRole` on `vmimport`;
- `DeregisterImage`, `DeleteSnapshot` and `ModifyImageAttribute` only on
  resources tagged `project=filnix`.

It cannot launch instances, create users or touch other buckets. The tag
rule is why the workflow tags at creation: an untagged snapshot or image
could not be made public or cleaned up.

## Rotating and tearing down

There is no key to rotate: each run gets 2-hour credentials from the OIDC
trust. To revoke, delete the `aws-ami` environment in GitHub or the role's
trust policy in IAM. To move to another account or region, recreate the
resources above there and change the three environment variables.

To remove everything:

1. Deregister the images and delete the snapshots tagged `project=filnix`
   (`aws ec2 describe-images --owners self --filters Name=tag:project,Values=filnix`).
2. Empty and delete the bucket.
3. Delete the roles `filnix-release-ami` and `vmimport`, and the OIDC
   provider if nothing else uses it.
4. Delete the `aws-ami` environment in the repository settings.

## filc.less.rest

`nixosConfigurations.demo-wiki` (nixos/demo-wiki.nix) is a public Fil-C
server: MediaWiki on Fil-C PHP-FPM behind Fil-C lighttpd, with SQLite, on
one t3.medium in this account, booted from the AMI. It is built to be
broken into at no cost:

- no IAM instance profile, and IMDSv2 required with a hop limit of 1;
- no tokens or private keys on the machine but its own TLS key, which
  lego (Go, a `filc.native` exception) gets from Let's Encrypt over HTTP-01;
- ports 80 and 443 open, 22 with keys only (root, the owner's key pair);
- the wiki is read-only for anonymous users, with account creation off;
- updates are pulled: `filnix-update.timer` switches to `demo-wiki` at the
  latest `v*` release every 6 hours with `max-jobs 0`, so it only
  substitutes from filc.cachix.org (the toplevel is in
  `scripts/ci-outputs.txt`). Nothing can push to it;
- https://filc.less.rest/status/ shows `filc-ps` every 5 minutes.

`scripts/launch-demo-wiki --ami AMI --tag vX --public-key KEY.pub` launches
it with an account session that may create instances (the release role
cannot). Without `--yes` it prints the commands. It creates, tagged
`project=filnix`: the security group and key pair `filnix-demo-wiki`, the
instance with user data `#filnix github:mbrock/filnix/vX#demo-wiki`, and an
Elastic IP. On first boot the AMI's `filnix-first-switch` service switches
to that configuration. Then point the `filc` A record in less.rest (on
DNSimple; the wildcard points elsewhere) at the Elastic IP; ACME succeeds
once it resolves (`systemctl start acme-order-renew-filc.less.rest` to retry
at once).

To take it down: terminate the instance, release the Elastic IP, delete the
security group and key pair `filnix-demo-wiki`, and remove the A record.
