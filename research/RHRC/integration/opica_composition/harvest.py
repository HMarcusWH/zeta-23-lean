"""Paginated read-only workflow accounting. Process success is not a finding."""
from __future__ import annotations
import json, os, re
from urllib.request import Request, build_opener, HTTPRedirectHandler
from urllib.parse import urlencode, urlparse
from .canonical import require, canonical_bytes

class _SameHostRedirect(HTTPRedirectHandler):
    def redirect_request(self,req,fp,code,msg,headers,newurl):
        require(urlparse(newurl).scheme=='https' and urlparse(newurl).hostname=='api.github.com',
                'credential-bearing cross-host redirect refused')
        return super().redirect_request(req,fp,code,msg,headers,newurl)

def github_reader(token=None):
    opener=build_opener(_SameHostRedirect())
    def get(path):
        require(path.startswith('/repos/') and '..' not in path,'unexpected GitHub API path')
        headers={'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28','User-Agent':'OPICA-ReadOnly-Harvest'}
        if token:headers['Authorization']='Bearer '+token
        with opener.open(Request('https://api.github.com'+path,headers=headers),timeout=60) as response:
            return json.load(response)
    return get

def paginate(get,path,key):
    rows=[];page=1
    while True:
        separator='&' if '?' in path else '?'
        result=get(path+separator+urlencode({'per_page':100,'page':page}))
        batch=result.get(key)
        require(type(batch)is list,'GitHub inventory response differs')
        rows.extend(batch)
        if len(batch)<100:break
        page+=1;require(page<=1000,'workflow pagination budget exceeded')
    return rows

def harvest_workflows(repository,head,*,get,classification:dict,scientific_records:dict,previous=None):
    require(re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+',repository) and
            re.fullmatch(r'[0-9a-f]{40}',head),'invalid repository/head')
    runs=paginate(get,f'/repos/{repository}/actions/runs?head_sha={head}','workflow_runs')
    output=[];previous=previous or {}
    for run in runs:
        require(run['head_sha']==head,'cross-source workflow result')
        jobs=paginate(get,f'/repos/{repository}/actions/runs/{run["id"]}/jobs?filter=all','jobs')
        for job in jobs:
            key=str(job['id']);rule=classification.get(run['path'],{}).get(job['name'])
            science=scientific_records.get(key)
            result={'run_id':run['id'],'event':run['event'],'run_attempt':job.get('run_attempt',run['run_attempt']),
                    'job_id':job['id'],'name':job['name'],'workflow':run['path'],'head':head,
                    'status':job['status'],'conclusion':job.get('conclusion'),
                    'classification':rule or 'UNCLASSIFIED','scientific_disposition':science or 'ARTIFACT_REVIEW_REQUIRED',
                    'previous_disposition':previous.get(key),'checked_checkout':'RESOLVE_FROM_SOURCE_BOUND_ARTIFACT'}
            result['disposition_changed']=science is not None and previous.get(key) is not None and science!=previous[key]
            output.append(result)
    require(len({r['job_id'] for r in output})==len(output),'duplicate physical job identity')
    return {'schema':'OPICA_COMPLETE_WORKFLOW_HARVEST_V1','requested_head':head,'jobs':output,
            'complete_process_accounting':all(r['status']=='completed' for r in output),
            'scientific_review_complete':bool(output) and all(r['scientific_disposition']!='ARTIFACT_REVIEW_REQUIRED' and
                r['classification']!='UNCLASSIFIED' for r in output),'RH':'OPEN','Step4':'OPEN'}
