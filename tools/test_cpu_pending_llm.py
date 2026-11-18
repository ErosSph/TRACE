import json
import unittest
from unittest.mock import patch
import cpu_pending_llm as m


class PendingLLMTransportTests(unittest.TestCase):
    def test_json_request_explicitly_disables_thinking_and_stays_unproved(self):
        class Response:
            status=200
            def __enter__(self):return self
            def __exit__(self,*args):pass
            def read(self,limit):
                return json.dumps(dict(choices=[dict(finish_reason='stop',message=dict(
                    content=json.dumps(dict(bindings=dict(slot='rule')))))] )).encode()
        class Opener:
            def open(self,request,timeout):
                body=json.loads(request.data)
                assert body['enable_thinking']is False
                assert body['response_format']=={'type':'json_object'}
                assert timeout==60
                return Response()
        with patch.object(m.urllib.request,'proxy_bypass',return_value=False),patch.object(
            m.urllib.request,'build_opener',return_value=Opener()):
            audit,answer=m.query({'slot':[{'id':'rule'}]},[],'test-not-a-credential')
        self.assertEqual(answer,{'slot':'rule'})
        self.assertEqual(audit['status'],'accepted_unproved')
        self.assertFalse(audit['enable_thinking'])
        self.assertNotIn('test-not-a-credential',json.dumps(audit))


if __name__=='__main__':unittest.main()
