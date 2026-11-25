import hashlib
import importlib.util
import io
import json
from pathlib import Path
import unittest
import urllib.request
import zipfile

spec = importlib.util.spec_from_file_location('fetch_manifest', Path(__file__).parents[1] / 'scripts/fetch-manifest.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class ArtifactTest(unittest.TestCase):
    def fixture(self):
        data = json.dumps({'commit': 'a' * 40, 'ci_run': 'https://github.com/tomhutchcroft/lrp/actions/runs/1'}).encode()
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, 'w') as z:
            z.writestr('manifest.json', data)
        archive = buf.getvalue()
        artifact = {'id': 2, 'expired': False, 'digest': 'sha256:' + hashlib.sha256(archive).hexdigest(), 'workflow_run': {'id': 1, 'head_sha': 'b' * 40}}
        run = {'id': 1, 'head_sha': 'b' * 40, 'status': 'completed', 'conclusion': 'success', 'html_url': 'https://github.com/tomhutchcroft/lrp/actions/runs/1'}
        return archive, artifact, run

    def test_binding_and_failure(self):
        archive, artifact, run = self.fixture()
        data, receipt = module.unpack_verified(archive, artifact, run, 'tomhutchcroft/lrp')
        self.assertEqual(receipt['manifest_sha256'], hashlib.sha256(data).hexdigest())
        with self.assertRaises(ValueError):
            module.unpack_verified(archive + b'changed', artifact, run, 'tomhutchcroft/lrp')
        run['conclusion'] = 'failure'
        with self.assertRaises(ValueError):
            module.unpack_verified(archive, artifact, run, 'tomhutchcroft/lrp')

    def test_redirect_drops_credentials(self):
        request = urllib.request.Request('https://api.github.com/archive', headers={'Authorization': 'Bearer test'})
        result = module.SafeRedirect().redirect_request(request, None, 302, 'Found', {}, 'https://blob.example/archive.zip')
        self.assertFalse(result.has_header('Authorization'))


if __name__ == '__main__':
    unittest.main()
