"""`scripts/build_distributions.py` gives source-bound, byte-reproducible artifacts.

Only the locked build tools are accepted; sdist normalization keeps every
member and byte while removing timestamps and ownership; a checkout with
uncommitted application files is detected; and two builds of the same source
give identical wheel and sdist digests (PKG-02). The two-build test needs the
locked build tools in the running interpreter, as the installed-distribution
test provides.
"""
from __future__ import annotations
import gzip
import io
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
import zipfile

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'scripts'))
import build_distributions as bd
sys.path.pop(0)

LOCK=(APP/'requirements-build.lock').read_text(encoding='utf-8')


def _installed(name):
    try:
        return version(name)
    except PackageNotFoundError:
        return None


LOCKED_TOOLS=all(_installed(name)==pin for name,pin in bd.locked_versions(LOCK).items())
HAS_SOURCE_PACKAGE=(APP/'src/permansson_app/__init__.py').is_file()


def _tarball(path,entries,mtime,owner):
    with tarfile.open(path,'w:gz') as archive:
        for name,data in entries:
            info=tarfile.TarInfo(name)
            info.mtime,info.uid,info.uname=mtime,owner,f'user{owner}'
            if data is None:
                info.type=tarfile.DIRTYPE
                archive.addfile(info)
            else:
                info.size=len(data)
                archive.addfile(info,io.BytesIO(data))


class BuildToolTests(unittest.TestCase):
    def test_only_the_locked_tools_are_accepted(self):
        pins=bd.locked_versions(LOCK)
        self.assertEqual(bd.check_tools(dict(pins),LOCK),pins)
        for name in ('setuptools','build'):
            for wrong in (None,'0.0.1',pins[name]+'.post1'):
                with self.subTest(name=name,installed=wrong),self.assertRaises(bd.BuildError):
                    bd.check_tools({**pins,name:wrong},LOCK)
        with self.assertRaises(bd.BuildError):
            bd.locked_versions('build==1.3.0 \\\n')

    def test_sdist_normalization_is_deterministic_and_lossless(self):
        entries=[('pkg-1/',None),('pkg-1/b.txt',b'second'),('pkg-1/PKG-INFO',b'Name: pkg')]
        with tempfile.TemporaryDirectory() as td:
            td=Path(td)
            _tarball(td/'one.tar.gz',entries,1000,1)
            _tarball(td/'two.tar.gz',list(reversed(entries)),2000,2)
            bd.normalize_sdist(td/'one.tar.gz',td/'n1.tar.gz',1793400000)
            bd.normalize_sdist(td/'two.tar.gz',td/'n2.tar.gz',1793400000)
            self.assertEqual((td/'n1.tar.gz').read_bytes(),(td/'n2.tar.gz').read_bytes())
            raw=(td/'n1.tar.gz').read_bytes()
            self.assertEqual(int.from_bytes(raw[4:8],'little'),1793400000)
            self.assertFalse(raw[3]&0x08,'gzip header carries a file name')
            with tarfile.open(td/'n1.tar.gz') as archive:
                members=archive.getmembers()
                self.assertEqual([m.name for m in members],sorted(n.rstrip('/') for n,_ in entries))
                self.assertTrue(all((m.mtime,m.uid,m.uname)==(1793400000,0,'') for m in members))
                self.assertEqual({m.name:archive.extractfile(m).read() for m in members if m.isfile()},
                                 {n:d for n,d in entries if d is not None})

    @unittest.skipUnless(shutil.which('git'),'needs git')
    def test_uncommitted_application_files_are_detected(self):
        with tempfile.TemporaryDirectory() as td:
            repo=Path(td)
            run=lambda *a:subprocess.run(['git',*a],cwd=repo,check=True,capture_output=True)
            run('init','-q');run('config','user.email','t@example.invalid');run('config','user.name','t')
            app=repo/'apps/x';app.mkdir(parents=True);(app/'f.txt').write_text('a')
            run('add','.');run('commit','-qm','c')
            identity=bd.source_identity(app)
            self.assertTrue(identity['clean'])
            self.assertEqual(identity['commit'],subprocess.run(['git','rev-parse','HEAD'],cwd=repo,
                             capture_output=True,text=True).stdout.strip())
            (app/'untracked.txt').write_text('b')
            self.assertFalse(bd.source_identity(app)['clean'])
            (app/'untracked.txt').unlink();(app/'f.txt').write_text('changed')
            self.assertFalse(bd.source_identity(app)['clean'])
        with tempfile.TemporaryDirectory() as td:
            self.assertIsNone(bd.source_identity(Path(td)))

    @unittest.skipUnless(LOCKED_TOOLS and HAS_SOURCE_PACKAGE,'needs the locked build tools and the package source')
    def test_two_builds_are_byte_identical(self):
        with tempfile.TemporaryDirectory() as td:
            td=Path(td)
            first=bd.build(td/'one',sys.executable,1793400000,require_clean=False)
            second=bd.build(td/'two',sys.executable,1793400000,require_clean=False)
            self.assertEqual((first['wheel'],first['sdist']),(second['wheel'],second['sdist']))
            names=zipfile.ZipFile(td/'one'/first['wheel']['name']).namelist()
            self.assertIn('permansson_app/__main__.py',names)
            with tarfile.open(td/'one'/first['sdist']['name']) as archive:
                self.assertTrue(any(n.endswith('/pyproject.toml') for n in archive.getnames()))
            self.assertEqual(first['evidence_status'],'LOCAL_SELF_PRODUCED_NOT_AUTHENTICATED')
            with self.assertRaises(bd.BuildError):
                bd.build(td/'one',sys.executable,1793400000,require_clean=False)


if __name__=='__main__':
    unittest.main()
