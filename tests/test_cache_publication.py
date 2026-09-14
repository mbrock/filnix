import importlib.util
import json
from pathlib import Path
import sqlite3
import subprocess
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    "publisher", Path(__file__).resolve().parents[1] / "scripts/publish-cache.py")
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)


def output(letter):
    return "/nix/store/" + letter * 32 + "-package"


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name)
        self.db = publisher.connect(self.directory / "publisher.sqlite")
        self.addCleanup(self.db.close)

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

    def test_disk_reserve_prevents_local_copy(self):
        publisher.enqueue(self.db,[output('a')],1)
        calls=[]
        publisher.publish(self.db,dict(directory=str(self.directory),
                          min_free_bytes=10**30,secret_key='/private/key'),
                          'local',64,run=lambda *a,**kw:calls.append(a))
        self.assertEqual(calls,[])
        self.assertEqual(publisher.report(self.db)['published'],0)


if __name__ == '__main__':
    unittest.main()
