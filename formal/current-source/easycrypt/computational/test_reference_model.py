from dataclasses import replace
import json, unittest
from reference_model import *

class T(unittest.TestCase):
 def setUp(self):
  self.k=Keys({"a":b"A","b":b"B","c":b"C"}); self.a=Principal("a","a1"); self.b=Principal("b","b1"); self.c=Principal("c","c1")
  fs=[]
  def add(i,kind,target,tag,cap=None):
   f=Fact(i,kind,self.a,tuple(x.id for x in fs),target,cap,tag).signed(self.k); fs.append(f)
  add("f1",FKind.GM,self.a,"ma"); add("f2",FKind.GC,self.a,"aa",Cap.ADMIN); add("f3",FKind.GC,self.a,"ah",Cap.HISTORY); add("f4",FKind.GC,self.a,"ap",Cap.PUNCTURE); add("f5",FKind.GC,self.a,"ab",Cap.BEE); add("f6",FKind.GM,self.b,"mb"); add("f7",FKind.GC,self.b,"be",Cap.EDIT)
  self.f=tuple(fs); self.auth=norm(self.f,self.a,self.k); self.ids=tuple(x.id for x in self.f); self.v=View(self.f,self.ids); self.s=State(self.a,"doc",frozenset({"n"}),{"n":frozenset(self.ids)})
 def fact(self,i,kind,ctx,target=None,cap=None,tag=None,obs=()): return Fact(i,kind,self.a,ctx,target,cap,tag,obs).signed(self.k)
 def env(self,**kw):
  d=dict(domain=DOMAIN,version=VERSION,doc="doc",oid="o",author=self.b,cap=Cap.EDIT,preds=("n",),adigest=self.auth.digest(),kind=Kind.EDIT,body={"action":"edit","payload":"x"},nonce="q"); d.update(kw); return Envelope(**d)
 def mut(self,op,c,v=None,s=None):
  self.assertFalse(validate(op,v or self.v,s or self.s,self.k).ok); self.assertTrue(validate(op,v or self.v,s or self.s,self.k,c).ok)
 def test_01_honest(self): self.assertTrue(validate(signop(self.env(),"b",self.k),self.v,self.s,self.k).ok)
 def test_02_noncanonical(self):
  o=signop(self.env(),"b",self.k); self.assertEqual(validate(replace(o,raw=json.dumps(json.loads(o.raw),indent=2).encode()),self.v,self.s,self.k).failed,"canonical-reencoding")
 def test_03_duplicate_preds(self):
  o=signop(self.env(),"b",self.k); x=json.loads(o.raw); x["directPredecessors"]=["n","n"]; self.assertEqual(validate(replace(o,raw=enc(x)),self.v,self.s,self.k).failed,"canonical-reencoding")
 def test_04_revoked_blocks(self):
  r=self.fact("f8",FKind.CR,self.ids,obs=("be",)); fs=(*self.f,r); a=norm(fs,self.a,self.k); v=View(fs,tuple(x.id for x in fs)); s=replace(self.s,nodes=frozenset({"nr"}),closures={"nr":frozenset(v.observed)}); o=signop(self.env(preds=("nr",),adigest=a.digest()),"b",self.k); self.assertEqual(validate(o,v,s,self.k).failed,"required-capability-active")
 def test_05_no_signature(self):
  o=replace(signop(self.env(),"b",self.k),sig=Sig("b","00")); self.mut(o,replace(Cfg(),signature=False))
 def test_06_no_author_key(self): self.mut(signop(self.env(),"a",self.k),replace(Cfg(),author_key=False))
 def test_07_no_incarnation(self):
  b2=Principal("b","b2"); r=self.fact("f8",FKind.MR,self.ids,obs=("mb",)); x=(*self.ids,"f8"); g=self.fact("f9",FKind.MG,x,b2,None,"mb2"); x=(*x,"f9"); h=self.fact("f10",FKind.CG,x,b2,Cap.EDIT,"be2"); fs=(*self.f,r,g,h); a=norm(fs,self.a,self.k); v=View(fs,tuple(z.id for z in fs)); s=replace(self.s,nodes=frozenset({"n2"}),closures={"n2":frozenset(v.observed)}); o=signop(self.env(preds=("n2",),adigest=a.digest()),"b",self.k); self.mut(o,replace(Cfg(),incarnation=False),v,s)
 def test_08_no_document(self): self.mut(signop(self.env(doc="other"),"b",self.k),replace(Cfg(),doc=False))
 def test_09_no_domain_version(self): self.mut(signop(self.env(domain="history",version=9),"b",self.k),replace(Cfg(),domver=False))
 def test_10_no_body_binding(self):
  o=signop(self.env(body={"action":"edit","payload":"old"}),"b",self.k,body=False); x=json.loads(o.raw); x["operationBody"]={"action":"edit","payload":"new"}; self.mut(replace(o,raw=enc(x)),replace(Cfg(),sig_body=False))
 def test_11_no_required_binding(self): self.mut(signop(self.env(body={"action":"delete-document","payload":"x"}),"b",self.k),replace(Cfg(),required_binding=False))
 def test_12_no_exact_context(self):
  r=self.fact("f8",FKind.CR,self.ids,obs=("be",)); self.mut(signop(self.env(),"b",self.k),replace(Cfg(),context=False),View(self.f,(*self.ids,r.id)))
 def test_13_no_auth_digest(self):
  q=self.fact("f8",FKind.MG,self.ids,self.c,None,"mc"); fs=(*self.f,q); v=View(fs,tuple(x.id for x in fs)); s=replace(self.s,nodes=frozenset({"nx"}),closures={"nx":frozenset(v.observed)}); self.mut(signop(self.env(preds=("nx",)),"b",self.k),replace(Cfg(),digest=False),v,s)
 def test_14_no_predecessor_complete(self):
  q=self.fact("f8",FKind.MG,self.ids,self.c,None,"mc"); s=replace(self.s,nodes=frozenset({"nx"}),closures={"nx":frozenset((*self.ids,q.id))}); self.mut(signop(self.env(preds=("nx",)),"b",self.k),replace(Cfg(),complete=False),self.v,s)
 def hist(self,recipient=None,merge="m",region=(("s",0,4),),cover=(("s","0",1),)):
  h=HistoryExpected(self.a,self.b,"m",(("s",0,4),),(("s","0",1),)); s=replace(self.s,history=h); body={"recipient":(recipient or self.b).j(),"mergeNode":merge,"region":[{"segment":x,"start":a,"end":b} for x,a,b in region],"cover":[{"segment":x,"path":p,"depth":d} for x,p,d in cover]}; e=self.env(author=self.a,cap=Cap.HISTORY,kind=Kind.HISTORY,body=body); return signop(e,"a",self.k),s
 def test_15_no_recipient(self): o,s=self.hist(self.c); self.mut(o,replace(Cfg(),recipient=False),s=s)
 def test_16_no_merge(self): o,s=self.hist(merge="x"); self.mut(o,replace(Cfg(),merge=False),s=s)
 def test_17_no_region(self): o,s=self.hist(region=(("s",0,8),)); self.mut(o,replace(Cfg(),region=False),s=s)
 def test_18_no_segment(self): o,s=self.hist(cover=(("z","0",1),)); self.mut(o,replace(Cfg(),segment=False),s=s)

if __name__=="__main__": unittest.main(verbosity=2)
