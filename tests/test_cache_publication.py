import importlib.util
import json
from pathlib import Path
import sqlite3
import subprocess
import tempfile
import unittest
import io
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    "publisher", Path(__file__).resolve().parents[1] / "scripts/publish-cache.py")
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)


def output(letter):
    return "/nix/store/" + letter * 32 + "-package"


class PublicationTests(unittest.TestCase):
    real_verify = staticmethod(publisher.verify)

    def test_native_discovery_validates_and_deduplicates_verified_feed(self):
        response = io.BytesIO(json.dumps(dict(watermark=42,paths=[output('b'),output('a'),output('a')])).encode())
        with patch.object(publisher.urllib.request,'urlopen',return_value=response):
            self.assertEqual(publisher.discover_native('http://127.0.0.1:8778/api/outputs'),
                             [output('a'),output('b')])
        for paths in ([output('a')+'.drv'],['/tmp/unrelated'],[None],'not-a-list'):
            with patch.object(publisher.urllib.request,'urlopen',
                              return_value=io.BytesIO(json.dumps(dict(paths=paths)).encode())):
                with self.assertRaisesRegex(ValueError,'invalid output path'):
                    publisher.discover_native('http://127.0.0.1:8778/api/outputs')

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name)
        self.db = publisher.connect(self.directory / "publisher.sqlite")
        self.addCleanup(self.db.close)
        # main() checks Cachix; test_verify_* cover that without the network.
        verify = patch.object(publisher, 'verify', return_value=[])
        verify.start()
        self.addCleanup(verify.stop)

    def test_discovery_includes_successful_dependency_of_failed_batch_only(self):
        source = self.directory / "experiment.sqlite"
        with sqlite3.connect(source) as db:
            db.executescript('''
                CREATE TABLE campaigns(id TEXT);
                CREATE TABLE candidates(drv TEXT,campaign TEXT);
                CREATE TABLE derivations(drv TEXT,outputs TEXT,available INTEGER);
                CREATE TABLE activities(drv TEXT,attempt TEXT);
                CREATE TABLE attempts(id TEXT,campaign TEXT,state TEXT);
                INSERT INTO campaigns VALUES('ours');
                INSERT INTO candidates VALUES('root','ours');
                INSERT INTO attempts VALUES('batch','ours','failed');
                INSERT INTO attempts VALUES('other','other','finished');
                INSERT INTO activities VALUES('dependency','batch');
                INSERT INTO activities VALUES('failed','batch');
                INSERT INTO activities VALUES('unrelated','other');
            ''')
            db.executemany("INSERT INTO derivations VALUES(?,?,?)", [
                (drv,json.dumps(dict(out=output(letter))),ready) for drv,letter,ready in [
                    ('root','a',1),('dependency','b',1),('failed','c',0),('unrelated','d',1)]])
        self.assertEqual(publisher.discover(source,'ours'),[output('a'),output('b')])
        with self.assertRaisesRegex(ValueError,'unknown campaign'):
            publisher.discover(source,'wrong')

    def test_duplicate_discovery_and_restart_preserve_receipts(self):
        publisher.enqueue(self.db,[output('a')],1)
        publisher.record(self.db,[output('a')],None,2)
        publisher.enqueue(self.db,[output('a'),output('b')],3)
        with sqlite3.connect(self.directory / 'publisher.sqlite') as restarted:
            self.assertEqual(restarted.execute('select published from outputs where path=?',
                                              (output('a'),)).fetchone()[0],2)
        self.assertEqual(publisher.report(self.db)['pending'],1)

    @patch.dict('os.environ',CREDENTIALS_DIRECTORY='/private/credentials')
    def test_failure_retries_individually_without_blocking_good_roots(self):
        publisher.enqueue(self.db,[output('a'),output('b')],1)
        def run(cmd,**kwargs):
            if output('a') in kwargs['input']:
                raise subprocess.CalledProcessError(1,cmd)
        with patch.object(publisher.time,'time',return_value=10):
            publisher.publish(self.db,dict(cache='filc'),'cachix',64,run=run)
        self.assertEqual(publisher.report(self.db)['published'],0)
        with patch.object(publisher.time,'time',return_value=71):
            publisher.publish(self.db,dict(cache='filc'),'cachix',64,run=run)
            publisher.publish(self.db,dict(cache='filc'),'cachix',64,run=run)
        self.assertEqual(publisher.report(self.db)['published'],1)
        self.assertEqual(publisher.report(self.db)['retrying'],1)

    @patch.dict('os.environ',CREDENTIALS_DIRECTORY='/private/credentials')
    def test_timeout_does_not_record_publication(self):
        publisher.enqueue(self.db,[output('a')],1)
        def timeout(cmd,**kwargs):
            raise subprocess.TimeoutExpired(cmd,10)
        publisher.publish(self.db,dict(cache='filc'),'cachix',64,run=timeout)
        self.assertEqual(publisher.report(self.db)['published'],0)
        self.assertEqual(publisher.report(self.db)['retrying'],1)

    def test_destinations_have_independent_receipts(self):
        publisher.enqueue(self.db,[output('a')],1)
        publisher.record(self.db,[output('a')],None,2)
        other=publisher.connect(self.directory/'other.sqlite')
        self.addCleanup(other.close)
        publisher.enqueue(other,[output('a')],1)
        self.assertEqual(publisher.report(other)['pending'],1)

    @patch.dict('os.environ',CREDENTIALS_DIRECTORY='/private/credentials')
    def test_republish_root_repairs_only_selected_destination_despite_stale_receipt(self):
        state = self.directory / 'state'
        state.mkdir()
        config = self.directory / 'config.json'
        config.write_text(json.dumps(dict(native_outputs_url='http://fixture/outputs',
                                          state=str(state),cachix=dict(cache='filc'))))
        for target in ('local','cachix'):
            with publisher.connect(state / (target + '.sqlite')) as db:
                publisher.enqueue(db,[output('a'),output('b')],1)
                publisher.record(db,[output('a'),output('b')],None,2)
                # A root with a stale receipt and a retry delay still needs repair.
                db.execute('update outputs set retry_after=1e30 where path=?',(output('b'),))
        pushed = []
        original = publisher.publish
        def run(cmd,**kwargs):
            pushed.extend(kwargs['input'].split())
        argv = ['publish','cachix','--config',str(config),'--republish-root',output('b')]
        with patch.object(publisher,'discover_native',return_value=[]), \
             patch.object(publisher,'publish',lambda *a,**k: original(*a,run=run,**k)):
            with patch('sys.argv',argv):
                publisher.main()
            with patch('sys.argv',argv[:-2]+['--extra-root',output('b')]):
                publisher.main()
        self.assertEqual(pushed,[output('b')])
        with sqlite3.connect(state / 'cachix.sqlite') as db:
            self.assertEqual(db.execute('select published from outputs where path=?',
                                        (output('a'),)).fetchone()[0],2)
            published,retry = db.execute('select published,retry_after from outputs where path=?',
                                         (output('b'),)).fetchone()
            self.assertGreater(published,2)
            self.assertEqual(retry,0)
        with sqlite3.connect(state / 'local.sqlite') as db:
            self.assertEqual(db.execute('select published,retry_after from outputs where path=?',
                                        (output('b'),)).fetchone(),(2,1e30))

    def test_disk_reserve_prevents_local_copy(self):
        publisher.enqueue(self.db,[output('a')],1)
        calls=[]
        publisher.publish(self.db,dict(directory=str(self.directory),
                          min_free_bytes=10**30,secret_key='/private/key'),
                          'local',64,run=lambda *a,**kw:calls.append(a))
        self.assertEqual(calls,[])
        self.assertEqual(publisher.report(self.db)['published'],0)



    @patch.dict('os.environ',CREDENTIALS_DIRECTORY='/private/credentials')
    def test_extra_roots_are_published_with_campaign_outputs(self):
        experiment=self.directory/'experiment'
        experiment.mkdir()
        with sqlite3.connect(experiment/'experiment.sqlite') as db:
            db.executescript('''
                CREATE TABLE campaigns(id TEXT);
                CREATE TABLE candidates(drv TEXT,campaign TEXT);
                CREATE TABLE derivations(drv TEXT,outputs TEXT,available INTEGER);
                CREATE TABLE activities(drv TEXT,attempt TEXT);
                CREATE TABLE attempts(id TEXT,campaign TEXT,state TEXT);
                INSERT INTO campaigns VALUES('ours');
                INSERT INTO candidates VALUES('root','ours');
            ''')
            db.execute("INSERT INTO derivations VALUES('root',?,1)",
                       (json.dumps(dict(out=output('a'))),))
        config=self.directory/'config.json'
        config.write_text(json.dumps(dict(campaign='ours',experiment=str(experiment),
                                          state=str(self.directory/'state'),
                                          cachix=dict(cache='filc'))))
        pushed=[]
        def run(cmd,**kwargs):
            pushed.extend(kwargs['input'].split())
        argv=['publish','cachix','--config',str(config),'--extra-root',output('t')]
        with patch('sys.argv',argv), \
             patch.object(publisher,'publish',
                          lambda *a,original=publisher.publish,**k: original(*a,run=run,**k)):
            publisher.main()
        self.assertEqual(sorted(pushed),[output('a'),output('t')])
        # Switch observation sources while retaining destination receipts.
        config.write_text(json.dumps(dict(native_outputs_url='http://127.0.0.1:8778/api/outputs',
                                          state=str(self.directory/'state'),
                                          cachix=dict(cache='filc'))))
        with patch('sys.argv',argv), \
             patch.object(publisher,'discover_native',return_value=[output('a'),output('b')]), \
             patch.object(publisher,'publish',
                          lambda *a,original=publisher.publish,**k: original(*a,run=run,**k)):
            publisher.main()
        self.assertEqual(sorted(pushed),[output('a'),output('b'),output('t')])
        # Disk images and container tarballs go to the local cache only.
        image='/nix/store/'+'i'*32+'-filnix-nixos-ami'
        tarball='/nix/store/'+'d'*32+'-filnix-php.tar.gz'
        dist='/nix/store/'+'o'*32+'-optfil-0.687-filnix-x86_64-linux.tar.xz'
        system='/nix/store/'+'s'*32+'-nixos-system-filc'
        with patch('sys.argv',argv), \
             patch.object(publisher,'references',
                          lambda p: [p, system] if p == image else []), \
             patch.object(publisher,'discover_native',return_value=[image,tarball,dist]), \
             patch.object(publisher,'publish',
                          lambda *a,original=publisher.publish,**k: original(*a,run=run,**k)):
            publisher.main()
        # The image stays off Cachix; the system it contains does not.
        self.assertEqual(sorted(pushed),[output('a'),output('b'),dist,system,output('t')])
        with patch('sys.argv',['publish','local','--config',str(config)]), \
             patch.object(publisher,'discover_native',return_value=[image]):
            config.write_text(json.dumps(dict(native_outputs_url='http://x',
                                              state=str(self.directory/'state'),
                                              local=dict(directory=str(self.directory/'cache'),
                                                         secret_key='k',min_free_bytes=0))))
            with patch.object(publisher,'publish',
                              lambda *a,original=publisher.publish,**k: original(*a,run=run,**k)):
                publisher.main()
        self.assertIn(image,pushed)
        with patch('sys.argv',argv[:-1]+['/nix/store/x.drv']), \
             self.assertRaises(SystemExit):
            publisher.main()

    def test_verify_clears_receipts_of_roots_cachix_lost(self):
        real = PublicationTests.real_verify
        kept, lost, image = output('k'), output('l'), '/nix/store/'+'i'*32+'-filnix-nixos-ami'
        pinned, dep_upstream, dep_lost = output('p'), output('u'), output('d')
        old, flaky = output('o'), output('f')
        publisher.enqueue(self.db,[kept,lost,image,pinned,old,flaky],1)
        publisher.record(self.db,[kept,lost,image,pinned,flaky],None,2)
        # Lost too, but published long ago: counted, not re-sent.
        publisher.record(self.db,[old],None,2-8*86400)
        with self.db:
            self.db.execute("INSERT INTO current VALUES('package',?)",(pinned,))
        cachix = {kept, pinned}
        upstream = {dep_upstream}
        checked = []
        def exists(cache, path):
            checked.append((cache, path))
            if path == flaky:
                return None  # a 429 or a timeout
            return path in (upstream if cache == publisher.UPSTREAM else cachix)
        closure = lambda root: [root, dep_upstream, dep_lost]
        config = dict(cache='filc')
        # One root and two closure paths per run, least recently checked first.
        cleared = set()
        for now in range(10, 70, 10):
            cleared |= set(real(self.db, config, 1, 2, now, exists=exists, requisites=closure))
        # The lost root and the root whose dependency no cache has; not the
        # dependency Cachix leaves to cache.nixos.org, nor the swa-only image.
        self.assertEqual(cleared, {lost, pinned})
        self.assertNotIn(image, {p for _, p in checked})
        published = {r[0] for r in self.db.execute(
            "SELECT path FROM outputs WHERE published IS NOT NULL")}
        self.assertEqual(published, {kept, image, old, flaky})
        # The rotation went past the unknown root to all the others.
        self.assertTrue({kept, lost, old} <= {p for _, p in checked})


if __name__ == '__main__':
    unittest.main()
