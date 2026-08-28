"""Executable Milestone-1 validator reference; not an EasyCrypt proof."""
from __future__ import annotations
from dataclasses import dataclass, replace
from enum import Enum
import hashlib, hmac, json
from typing import Any

DOMAIN, VERSION = "facets-causal-dag", 1

class Cap(str, Enum):
    EDIT="edit"; ADMIN="admin"; HISTORY="history-grant"; PUNCTURE="puncture"; BEE="beekem-update"
class Kind(str, Enum):
    EDIT="edit"; ADD="add-member"; REMOVE="remove-member"; GRANT="grant-capability"; REVOKE="revoke-capability"; BEE="beekem-update"; HISTORY="history-grant"; PUNCTURE="puncture"
class FKind(str, Enum):
    GM="genesis-member"; GC="genesis-capability"; MG="membership-grant"; MR="membership-revoke"; CG="capability-grant"; CR="capability-revoke"

@dataclass(frozen=True, order=True)
class Principal:
    vk:str; inc:str
    def j(self): return {"verificationKey":self.vk,"incarnationNonce":self.inc}

@dataclass(frozen=True)
class Sig: vk:str; mac:str

class Keys:
    def __init__(self, secrets:dict[str,bytes]): self.s=secrets
    def sign(self,vk:str,msg:bytes)->Sig: return Sig(vk,hmac.new(self.s[vk],msg,hashlib.sha256).hexdigest())
    def ok(self,sig:Sig,msg:bytes)->bool:
        k=self.s.get(sig.vk)
        return k is not None and hmac.compare_digest(sig.mac,hmac.new(k,msg,hashlib.sha256).hexdigest())

def enc(x:Any)->bytes: return json.dumps(x,sort_keys=True,separators=(",",":"),allow_nan=False).encode()
def pobj(x:Any)->Principal:
    if not isinstance(x,dict) or set(x)!={"verificationKey","incarnationNonce"}: raise ValueError
    return Principal(x["verificationKey"],x["incarnationNonce"])

@dataclass(frozen=True)
class Fact:
    id:str; kind:FKind; issuer:Principal; ctx:tuple[str,...]; target:Principal|None=None; cap:Cap|None=None; tag:str|None=None; observed:tuple[str,...]=(); sig:Sig|None=None
    def tr(self): return enc({"domain":"protocol-authorization-fact","version":VERSION,"id":self.id,"kind":self.kind.value,"issuer":self.issuer.j(),"context":sorted(set(self.ctx)),"target":None if self.target is None else self.target.j(),"capability":None if self.cap is None else self.cap.value,"tag":self.tag,"observed":sorted(set(self.observed))})
    def signed(self,k:Keys): return replace(self,sig=k.sign(self.issuer.vk,self.tr()))

@dataclass(frozen=True)
class Auth:
    members:tuple[tuple[str,Principal],...]=(); rm:tuple[str,...]=(); caps:tuple[tuple[str,Principal,Cap],...]=(); rc:tuple[str,...]=(); retired:tuple[Principal,...]=(); ids:tuple[str,...]=()
    def active(self,p:Principal,exact=True): return any(t not in self.rm and (q==p if exact else q.vk==p.vk) for t,q in self.members)
    def has(self,p:Principal,c:Cap,exact=True): return any(t not in self.rc and (q==p if exact else q.vk==p.vk) and x==c for t,q,x in self.caps)
    def digest(self): return hashlib.sha256(enc({"members":[(t,p.j()) for t,p in self.members],"removedMembers":self.rm,"capabilities":[(t,p.j(),c.value) for t,p,c in self.caps],"removedCapabilities":self.rc,"retired":[p.j() for p in self.retired],"facts":self.ids})).hexdigest()

def norm(facts:tuple[Fact,...], creator:Principal, keys:Keys)->Auth:
    states={frozenset():Auth()}; st=Auth()
    for f in facts:
        cs=frozenset(f.ctx)
        if tuple(sorted(cs))!=f.ctx or cs not in states or f.id in st.ids or f.sig is None or f.sig.vk!=f.issuer.vk or not keys.ok(f.sig,f.tr()): raise ValueError("invalid-fact")
        at=states[cs]; genesis=f.kind in {FKind.GM,FKind.GC}
        if genesis:
            if f.issuer!=creator or cs!=frozenset(st.ids): raise ValueError("genesis")
        elif not at.active(f.issuer) or not at.has(f.issuer,Cap.ADMIN): raise ValueError("issuer")
        m=dict(st.members); rm=set(st.rm); c={t:(p,x) for t,p,x in st.caps}; rc=set(st.rc); retired=set(st.retired)
        if f.kind in {FKind.GM,FKind.MG}:
            if f.target is None or not f.tag or f.target in retired or f.tag in m: raise ValueError("grant")
            m[f.tag]=f.target
        elif f.kind==FKind.MR:
            if not f.observed or any(t not in m for t in f.observed): raise ValueError("revoke")
            for t in f.observed: rm.add(t); retired.add(m[t])
        elif f.kind in {FKind.GC,FKind.CG}:
            if f.target is None or f.cap is None or not f.tag or f.tag in c: raise ValueError("cap-grant")
            c[f.tag]=(f.target,f.cap)
        elif f.kind==FKind.CR:
            if not f.observed or any(t not in c for t in f.observed): raise ValueError("cap-revoke")
            rc.update(f.observed)
        st=Auth(tuple(sorted(m.items())),tuple(sorted(rm)),tuple(sorted((t,p,x) for t,(p,x) in c.items())),tuple(sorted(rc)),tuple(sorted(retired)),tuple(sorted((*st.ids,f.id))))
        states[frozenset(st.ids)]=st
    return st

@dataclass(frozen=True)
class Envelope:
    domain:str; version:int; doc:str; oid:str; author:Principal; cap:Cap; preds:tuple[str,...]; adigest:str; kind:Kind; body:dict[str,Any]; nonce:str
    def wirej(self): return {"protocolDomain":self.domain,"protocolVersion":self.version,"documentId":self.doc,"operationId":self.oid,"author":self.author.j(),"requiredCapability":self.cap.value,"directPredecessors":sorted(set(self.preds)),"authorizationDigest":self.adigest,"operationKind":self.kind.value,"operationBody":self.body,"nonce":self.nonce}
    def tr(self,body=True,cap=True): return enc({"transcriptDomain":"protocol-operation",**self.wirej(),"operationBody":self.body if body else None,"requiredCapability":self.cap.value if cap else None})
    def wire(self): return enc(self.wirej())
    @staticmethod
    def parse(raw:bytes):
        x=json.loads(raw); need={"protocolDomain","protocolVersion","documentId","operationId","author","requiredCapability","directPredecessors","authorizationDigest","operationKind","operationBody","nonce"}
        if set(x)!=need or not isinstance(x["directPredecessors"],list) or not isinstance(x["operationBody"],dict): raise ValueError
        return Envelope(x["protocolDomain"],x["protocolVersion"],x["documentId"],x["operationId"],pobj(x["author"]),Cap(x["requiredCapability"]),tuple(x["directPredecessors"]),x["authorizationDigest"],Kind(x["operationKind"]),x["operationBody"],x["nonce"])

@dataclass(frozen=True)
class SignedOp: raw:bytes; sig:Sig

def signop(e:Envelope,vk:str,k:Keys,body=True,cap=True): return SignedOp(e.wire(),k.sign(vk,e.tr(body,cap)))

@dataclass(frozen=True)
class View: facts:tuple[Fact,...]; observed:tuple[str,...]
@dataclass(frozen=True)
class HistoryExpected: issuer:Principal; recipient:Principal; merge:str; region:tuple[tuple[str,int,int],...]; cover:tuple[tuple[str,str,int],...]
@dataclass(frozen=True)
class State:
    creator:Principal; doc:str; nodes:frozenset[str]; closures:dict[str,frozenset[str]]; seen_oids:frozenset[str]=frozenset(); seen_nonces:frozenset[str]=frozenset(); bee_paths:dict[tuple[str,...],str]|None=None; history:HistoryExpected|None=None; punctures:frozenset[str]=frozenset()
    def closure(self,preds):
        z=set()
        for p in preds:
            if p not in self.closures: return None
            z|=set(self.closures[p])
        return frozenset(z)

@dataclass(frozen=True)
class Cfg:
    canonical:bool=True; domver:bool=True; doc:bool=True; fresh:bool=True; complete:bool=True; context:bool=True; digest:bool=True; signature:bool=True; author_key:bool=True; incarnation:bool=True; body_policy:bool=True; required_binding:bool=True; add_fresh:bool=True; bee:bool=True; recipient:bool=True; merge:bool=True; region:bool=True; segment:bool=True; puncture:bool=True; sig_body:bool=True; sig_cap:bool=True

@dataclass(frozen=True)
class Result: ok:bool; failed:str|None

def policy(e:Envelope)->Cap:
    if e.kind==Kind.EDIT: return Cap.ADMIN if e.body.get("action")=="delete-document" else Cap.EDIT
    return {Kind.ADD:Cap.ADMIN,Kind.REMOVE:Cap.ADMIN,Kind.GRANT:Cap.ADMIN,Kind.REVOKE:Cap.ADMIN,Kind.BEE:Cap.BEE,Kind.HISTORY:Cap.HISTORY,Kind.PUNCTURE:Cap.PUNCTURE}[e.kind]
def bodyok(e:Envelope):
    if e.kind==Kind.EDIT: return set(e.body)<={"action","payload"} and isinstance(e.body.get("payload"),str) and bool(e.body["payload"])
    if e.kind==Kind.BEE: return set(e.body)=={"author","path"}
    if e.kind==Kind.HISTORY: return set(e.body)=={"recipient","mergeNode","region","cover"}
    if e.kind==Kind.PUNCTURE: return set(e.body)=={"region"}
    return bool(e.body)
def pregion(x):
    z=tuple((i["segment"],i["start"],i["end"]) for i in x)
    if z!=tuple(sorted(set(z))) or any(a<0 or b<=a for _,a,b in z): raise ValueError
    return z
def pcover(x):
    z=tuple((i["segment"],i["path"],i["depth"]) for i in x)
    if z!=tuple(sorted(set(z))) or any(d<0 for _,_,d in z): raise ValueError
    return z

def validate(op:SignedOp,v:View,s:State,k:Keys,c:Cfg=Cfg())->Result:
    try: e=Envelope.parse(op.raw)
    except Exception: return Result(False,"canonical-decoding")
    if c.canonical and op.raw!=e.wire(): return Result(False,"canonical-reencoding")
    if c.domver and (e.domain!=DOMAIN or e.version!=VERSION): return Result(False,"domain-version")
    if c.doc and e.doc!=s.doc: return Result(False,"document-binding")
    if c.fresh and (not e.oid or not e.nonce or e.oid in s.seen_oids or e.nonce in s.seen_nonces): return Result(False,"freshness")
    if any(p not in s.nodes for p in e.preds): return Result(False,"missing-predecessor")
    cl=s.closure(e.preds)
    ids=tuple(sorted(f.id for f in v.facts))
    if c.complete and frozenset(ids)!=cl: return Result(False,"predecessor-completeness")
    if c.context and tuple(sorted(v.observed))!=ids: return Result(False,"exact-author-context")
    try: a=norm(v.facts,s.creator,k)
    except ValueError: return Result(False,"authorization-facts")
    if c.digest and e.adigest!=a.digest(): return Result(False,"authorization-digest")
    if c.author_key and op.sig.vk!=e.author.vk: return Result(False,"author-key-binding")
    if c.signature and not k.ok(op.sig,e.tr(c.sig_body,c.sig_cap)): return Result(False,"operation-signature")
    if not a.active(e.author,c.incarnation): return Result(False,"active-incarnation")
    if not a.has(e.author,e.cap,c.incarnation): return Result(False,"required-capability-active")
    if c.required_binding and policy(e)!=e.cap: return Result(False,"required-capability-binding")
    if c.body_policy and not bodyok(e): return Result(False,"operation-body-policy")
    if e.kind==Kind.ADD and c.add_fresh:
        try: q=pobj(e.body["target"])
        except Exception: return Result(False,"add-target")
        if q in {p for _,p in a.members} or q in a.retired or q.inc==e.author.inc: return Result(False,"add-target-freshness")
    if e.kind==Kind.BEE and c.bee:
        path=(s.bee_paths or {}).get(tuple(sorted(set(e.preds))))
        if e.body.get("author")!=e.author.j() or e.body.get("path")!=path: return Result(False,"beekem-path")
    if e.kind==Kind.HISTORY:
        h=s.history
        try: r=pobj(e.body["recipient"]); m=e.body["mergeNode"]; rg=pregion(e.body["region"]); cv=pcover(e.body["cover"])
        except Exception: return Result(False,"history-encoding")
        if h is None or h.issuer!=e.author: return Result(False,"history-expectation")
        if c.recipient and r!=h.recipient: return Result(False,"recipient-binding")
        if c.merge and m!=h.merge: return Result(False,"merge-binding")
        if c.region and rg!=h.region: return Result(False,"region-binding")
        if c.segment and (cv!=h.cover or any(seg not in {x for x,_,_ in rg} for seg,_,_ in cv)): return Result(False,"segment-binding")
    if e.kind==Kind.PUNCTURE and c.puncture and (e.cap!=Cap.PUNCTURE or e.body.get("region") not in s.punctures): return Result(False,"puncture-policy")
    return Result(True,None)
