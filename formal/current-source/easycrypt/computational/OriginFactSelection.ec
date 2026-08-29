require import AllCore List FSet.
require import ProtocolTypes CanonicalEncoding ProtocolPrimitives.
require import UnauthorizedSignatureReduction UnauthorizedOriginGame.
require import OriginFactVerificationEvidence.

import PG.

(* Select the first authorization-fact signature whose exact issuer/message
   pair was not returned by the protocol signing interface.  The candidate is
   built from the same signed fact that the production normalizer processed. *)
op first_unoriginated_fact_forgery
    (facts : signed_authorization_fact list)
    (sign_queries : PG.signature_query list) :
    PG.signature_forgery option =
  with facts = [] => None
  with facts = signed_fact :: rest =>
    if fact_signature_originated signed_fact sign_queries
    then first_unoriginated_fact_forgery rest sign_queries
    else Some (fact_signature_forgery_candidate signed_fact).

lemma first_unoriginated_fact_forgery_none_iff_all_originated
    (facts : signed_authorization_fact list)
    (sign_queries : PG.signature_query list) :
  first_unoriginated_fact_forgery facts sign_queries = None <=>
  all_fact_signatures_originated facts sign_queries.
proof.
  elim: facts => [| signed_fact rest ih] //=.
  case: (fact_signature_originated signed_fact sign_queries) => //=.
  by rewrite ih.
qed.

lemma first_unoriginated_fact_forgery_has_source
    (facts : signed_authorization_fact list)
    (sign_queries : PG.signature_query list) :
  first_unoriginated_fact_forgery facts sign_queries <> None =>
  exists signed_fact,
       mem facts signed_fact
    /\ ! fact_signature_originated signed_fact sign_queries
    /\ first_unoriginated_fact_forgery facts sign_queries =
         Some (fact_signature_forgery_candidate signed_fact).
proof.
  elim: facts => [| signed_fact rest ih] //=.
  case: (fact_signature_originated signed_fact sign_queries) => originated.
  + move=> selected.
    have [source [in_rest [not_originated source_selected]]] := ih selected.
    exists source.
    by rewrite in_cons source_selected; smt().
  + move=> _.
    exists signed_fact.
    by rewrite in_cons originated.
qed.

lemma first_unoriginated_fact_forgery_is_valid
    (facts : signed_authorization_fact list)
    (sign_queries : PG.signature_query list)
    (verify_queries : PG.signature_verification_query list) :
  first_unoriginated_fact_forgery facts sign_queries <> None =>
  (forall signed_fact,
     mem facts signed_fact =>
     signed_fact_verification_logged signed_fact verify_queries) =>
  PG.signature_forgery_valid
    (oget (first_unoriginated_fact_forgery facts sign_queries))
    sign_queries verify_queries.
proof.
  move=> selected all_logged.
  have [signed_fact [in_facts [not_originated selected_eq]]] :=
    first_unoriginated_fact_forgery_has_source
      facts sign_queries selected.
  rewrite selected_eq /=.
  exact (accepted_unoriginated_fact_candidate_is_forgery
    signed_fact sign_queries verify_queries
    (all_logged signed_fact in_facts) not_originated).
qed.

lemma not_all_originated_selects_valid_fact_forgery
    (facts : signed_authorization_fact list)
    (sign_queries : PG.signature_query list)
    (verify_queries : PG.signature_verification_query list) :
  ! all_fact_signatures_originated facts sign_queries =>
  (forall signed_fact,
     mem facts signed_fact =>
     signed_fact_verification_logged signed_fact verify_queries) =>
     first_unoriginated_fact_forgery facts sign_queries <> None
  /\ PG.signature_forgery_valid
       (oget (first_unoriginated_fact_forgery facts sign_queries))
       sign_queries verify_queries.
proof.
  move=> not_all all_logged.
  have selected :
    first_unoriginated_fact_forgery facts sign_queries <> None.
  + rewrite first_unoriginated_fact_forgery_none_iff_all_originated.
    exact not_all.
  split; first exact selected.
  exact (first_unoriginated_fact_forgery_is_valid
    facts sign_queries verify_queries selected all_logged).
qed.
