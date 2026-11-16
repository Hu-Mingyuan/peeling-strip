#!/usr/bin/env python3
"""Build the pinned FG strip library, final consumers, and transitive axiom audit."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'verification'
ENV = dict(os.environ)
ENV.setdefault('MATHLIB_NO_CACHE_ON_UPDATE', '1')
ENV.setdefault('LEAN_NUM_THREADS', '2')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REQUIRED_ROOTS = {'FgStrip.Proposition74.ambient', 'FgStrip.Proposition74.triangulation',
                  'FgStrip.Rounds.rounds'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def library_snapshot():
    paths = sorted((ROOT / 'FgStrip').rglob('*.lean')) + [ROOT / 'FgStrip.lean']
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in paths}


def source_snapshot():
    result = library_snapshot()
    for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                 'verification/FullConsumer.lean', 'verification/AxiomAudit.lean',
                 'verification/accepted-library.json', 'scripts/verify.py'):
        result[name] = digest(ROOT / name)
    return result


def dependency_revisions():
    pins = {}
    for package in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']:
        if package['type'] != 'git':
            raise RuntimeError(f'Unexpected dependency type: {package["name"]}')
        command = ['git', '-C', str(ROOT / '.lake/packages' / package['name'])]
        actual = subprocess.check_output(command + ['rev-parse', 'HEAD'], text=True, env=ENV).strip()
        if actual != package['rev']:
            raise RuntimeError(f'Unexpected revision for {package["name"]}: {actual}')
        if subprocess.check_output(command + ['status', '--porcelain', '--untracked-files=all'], env=ENV):
            raise RuntimeError(f'Modified dependency worktree: {package["name"]}')
        pins[package['name']] = actual
    return pins


def run(args, log):
    started = time.monotonic()
    print('Checking:', ' '.join(args), flush=True)
    path = EVIDENCE / log
    with path.open('w', encoding='utf-8') as stream:
        proc = subprocess.run(args, cwd=ROOT, env=ENV, stdout=stream, stderr=subprocess.STDOUT)
    output = path.read_text(encoding='utf-8')
    if proc.returncode or re.search(r"\bsorryAx\b|\bdeclaration uses ['\"]sorry['\"]|\badmitted\b", output):
        print(output[-16000:], end='')
        raise RuntimeError(f'Check failed; full output: {path.relative_to(ROOT)}')
    print(f'Passed in {time.monotonic() - started:.1f}s; log: {path.relative_to(ROOT)}', flush=True)
    return output


def audit_roots(source, output):
    expected = set(re.findall(r'^#print axioms (\S+)', source, re.M))
    entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", output)
    reported = {name for name, _ in entries} | set(no_axioms)
    if expected != reported:
        raise RuntimeError(f'Axiom declaration mismatch: {expected ^ reported}')
    for name, raw in entries:
        actual = {x.strip() for x in raw.split(',') if x.strip()}
        if actual - ALLOWED:
            raise RuntimeError(f'Unexpected axioms for {name}: {actual - ALLOWED}')
    return sorted(reported)


def main():
    EVIDENCE.mkdir(exist_ok=True)
    receipt = EVIDENCE / 'publication-check.json'
    result = {'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'status': 'running', 'scope': 'all project modules, both final consumers, transitive axioms'}
    receipt.write_text(json.dumps(result, indent=2) + '\n')
    try:
        accepted = json.loads((EVIDENCE / 'accepted-library.json').read_text())
        if library_snapshot() != accepted['source_sha256']:
            raise RuntimeError('Library differs from the accepted source manifest')
        before = source_snapshot()
        pins = dependency_revisions()
        version = run(['lean', '--version'], 'toolchain.log').strip()
        if 'version 4.34.1,' not in version:
            raise RuntimeError(f'Unexpected Lean version: {version}')
        run(['lake', '--rehash', 'build', 'FgStrip'], 'build.log')
        consumer = run(['lake', 'env', 'lean', 'verification/FullConsumer.lean'], 'final-consumer.log')
        consumer_roots = audit_roots((EVIDENCE / 'FullConsumer.lean').read_text(), consumer)
        audit = run(['lake', 'env', 'lean', 'verification/AxiomAudit.lean'], 'axioms.log')
        roots = audit_roots((EVIDENCE / 'AxiomAudit.lean').read_text(), audit)
        if not REQUIRED_ROOTS <= set(roots):
            raise RuntimeError('A required final theorem is absent from the axiom audit')
        audited = dict(re.findall(r'AUDITED (FgStrip(?:\.[\w.]+)?): (\d+) declarations', audit))
        expected_modules = {'.'.join(Path(p).with_suffix('').parts) for p in library_snapshot()}
        if set(audited) != expected_modules:
            raise RuntimeError(f'Module audit mismatch: {expected_modules ^ set(audited)}')
        if not sum(map(int, audited.values())):
            raise RuntimeError('No project declarations audited')
        if dependency_revisions() != pins or source_snapshot() != before:
            raise RuntimeError('Verification inputs or dependencies changed during verification')
        result.update(status='passed', lean_version=version, dependency_commits=pins,
                      dependency_worktrees_clean=True, source_stability_verified=True,
                      accepted_library_commit=accepted['accepted_commit'],
                      final_targets=sorted(REQUIRED_ROOTS), allowed_axioms=sorted(ALLOWED),
                      audited_final_declarations=roots, consumer_roots=consumer_roots,
                      audited_modules={k: int(v) for k, v in audited.items()},
                      source_sha256=before,
                      evidence_sha256={name: digest(EVIDENCE / name) for name in
                                       ('toolchain.log', 'build.log', 'final-consumer.log', 'axioms.log')})
    except BaseException as exc:
        result.update(status='failed', error=str(exc))
        raise
    finally:
        result['finished_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        receipt.write_text(json.dumps(result, indent=2) + '\n')
    print('FG_STRIP_PROPOSITION74_VERIFIED')


if __name__ == '__main__':
    main()
