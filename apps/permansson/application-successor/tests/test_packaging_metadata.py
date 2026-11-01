"""Package metadata stays truthful and reproducible.

The declared build backend is the hash-locked one, the runtime pins agree with
the runtime lock, the version is the owner-selected release version, and the
description and classifiers state the qualified Linux CPython 3.12/3.13 scope
without calling the package numeric-only.
"""
from __future__ import annotations
from pathlib import Path
import re
import tomllib
import unittest

APP=Path(__file__).resolve().parents[1]


def locked(name:str,lock:str)->str:
    match=re.search(rf'^{re.escape(name)}==([^\s\\]+)',lock,re.M)
    if match is None:
        raise AssertionError(f'{name} is not pinned in the lock')
    return match.group(1)


def backend_problems(pyproject:dict,build_lock:str)->list[str]:
    system=pyproject.get('build-system',{})
    problems=[]
    if system.get('build-backend')!='setuptools.build_meta':
        problems.append('unexpected build backend')
    if system.get('requires')!=[f'setuptools=={locked("setuptools",build_lock)}']:
        problems.append(f'build requires {system.get("requires")} differ from the locked setuptools')
    return problems


class PackagingMetadataTests(unittest.TestCase):
    def setUp(self):
        self.pyproject=tomllib.loads((APP/'pyproject.toml').read_text(encoding='utf-8'))
        self.build_lock=(APP/'requirements-build.lock').read_text(encoding='utf-8')
        self.runtime_lock=(APP/'requirements-runtime.lock').read_text(encoding='utf-8')

    def test_build_backend_is_the_locked_one(self):
        self.assertEqual(backend_problems(self.pyproject,self.build_lock),[])
        for requires in (['setuptools>=64'],['setuptools'],['setuptools==80.0.0'],['setuptools==84.2.1','wheel']):
            changed={**self.pyproject,'build-system':{**self.pyproject['build-system'],'requires':requires}}
            with self.subTest(requires=requires):
                self.assertTrue(backend_problems(changed,self.build_lock))
        changed={**self.pyproject,'build-system':{**self.pyproject['build-system'],'build-backend':'flit_core.buildapi'}}
        self.assertTrue(backend_problems(changed,self.build_lock))

    def test_runtime_dependencies_match_the_runtime_lock(self):
        for requirement in self.pyproject['project']['dependencies']:
            name,version=requirement.split('==')
            with self.subTest(name=name):
                self.assertEqual(locked(name,self.runtime_lock),version)
        # The documented `[full-schema]` extra is a compatibility alias of the mandatory pins.
        self.assertEqual(sorted(self.pyproject['project']['optional-dependencies']['full-schema']),
                         sorted(self.pyproject['project']['dependencies']))

    def test_version_and_description_do_not_overstate(self):
        # The owner selected 0.2.0 for the first numeric release (2026-11-01).
        # Choosing a version authorizes nothing: release activation is the
        # owner's dispatch of the release workflow, checked by the release gate.
        project=self.pyproject['project']
        self.assertEqual(project['version'],'0.2.0')
        init=(APP/'src/permansson_app/__init__.py').read_text(encoding='utf-8')
        self.assertIn(f'__version__ = "{project["version"]}"',init)
        self.assertNotIn('numeric-only',project['description'].lower())
        self.assertNotIn('draft',project['description'].lower())
        self.assertEqual(project['requires-python'],'>=3.12,<3.14')
        classifiers=set(project['classifiers'])
        self.assertTrue({'Operating System :: POSIX :: Linux','Programming Language :: Python :: 3.12',
                         'Programming Language :: Python :: 3.13'}<=classifiers)
        self.assertFalse([c for c in classifiers if 'Windows' in c or 'MacOS' in c or ':: 3.11' in c])
