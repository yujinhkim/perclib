#!/usr/bin/env python3
"""Download one successful CI artifact and bind its manifest to a local receipt.

Uses GitHub REST and Python's standard library. No Lean invocation; no status ledger.
"""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import urllib.request
import zipfile

LIMIT = 64 * 1024 * 1024


def unpack_verified(archive, artifact, run, repository):
    if not re.fullmatch(r'tomhutchcroft/(lrp|perclib)', repository):
        raise ValueError('Unexpected repository')
    if run['status'] != 'completed' or run['conclusion'] != 'success':
        raise ValueError('Workflow has not completed successfully')
    run_url = f'https://github.com/{repository}/actions/runs/{run["id"]}'
    if run['html_url'] != run_url or artifact['workflow_run']['id'] != run['id']:
        raise ValueError('Artifact is not associated with this repository/run')
    if artifact['expired'] or artifact['workflow_run']['head_sha'] != run['head_sha']:
        raise ValueError('Expired artifact or head mismatch')
    archive_hash = hashlib.sha256(archive).hexdigest()
    if artifact.get('digest') != 'sha256:' + archive_hash:
        raise ValueError('Downloaded archive does not match GitHub artifact digest')
    with zipfile.ZipFile(io.BytesIO(archive)) as z:
        names = [n for n in z.namelist() if n.split('/')[-1] == 'manifest.json']
        if len(names) != 1 or z.getinfo(names[0]).file_size > LIMIT:
            raise ValueError('Expected exactly one reasonably sized manifest.json')
        content = z.read(names[0])
    manifest = json.loads(content)
    if manifest.get('ci_run') != run_url or not re.fullmatch('[a-f0-9]{40}', manifest.get('commit', '')):
        raise ValueError('Manifest provenance does not match the successful run')
    # A PR's checkout can be the synthetic merge, rather than run.head_sha.
    receipt = {'schema': 'perclib-artifact-receipt-v1', 'repository': repository,
               'manifest_sha256': hashlib.sha256(content).hexdigest(),
               'archive_sha256': archive_hash,
               'artifact': {k: artifact[k] for k in ('id', 'workflow_run', 'expired', 'digest')},
               'run': {k: run[k] for k in ('id', 'head_sha', 'status', 'conclusion', 'html_url')}}
    return content, receipt


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        redirected = super().redirect_request(req, fp, code, msg, headers, newurl)
        # GitHub redirects archive downloads to signed blob URLs. Never forward the token.
        if urllib.parse.urlsplit(req.full_url).netloc != urllib.parse.urlsplit(newurl).netloc:
            redirected.remove_header('Authorization')
        return redirected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('artifact_id', type=int)
    parser.add_argument('--repository', default='tomhutchcroft/lrp')
    parser.add_argument('--output', type=Path, default=Path('wiki/.artifacts'))
    args = parser.parse_args()
    if not re.fullmatch(r'tomhutchcroft/(lrp|perclib)', args.repository):
        parser.error('Unexpected repository')
    opener = urllib.request.build_opener(SafeRedirect())
    base = f'https://api.github.com/repos/{args.repository}'
    def get(suffix):
        headers = {'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28'}
        token = os.environ.get('GH_TOKEN') or os.environ.get('GITHUB_TOKEN')
        if token:
            headers['Authorization'] = 'Bearer ' + token
        with opener.open(urllib.request.Request(base + suffix, headers=headers), timeout=60) as response:
            data = response.read(LIMIT + 1)
        if len(data) > LIMIT:
            raise ValueError('Artifact exceeds download size limit')
        return data
    artifact = json.loads(get(f'/actions/artifacts/{args.artifact_id}'))
    run = json.loads(get(f'/actions/runs/{artifact["workflow_run"]["id"]}'))
    if run['conclusion'] != 'success' or run['status'] != 'completed':
        raise ValueError('Workflow has not completed successfully')
    content, receipt = unpack_verified(get(f'/actions/artifacts/{args.artifact_id}/zip'), artifact, run, args.repository)
    args.output.mkdir(parents=True, exist_ok=True)
    # A partial update fails the manifest-byte binding at build time.
    (args.output / 'manifest.json').write_bytes(content)
    (args.output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'Wrote verified artifact {args.artifact_id} to {args.output}')


if __name__ == '__main__':
    main()
