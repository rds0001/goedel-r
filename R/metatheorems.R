.metatheorem_resource_sha <- "faae76a30fa713fb151a6ca8cb535c3aeafbd0fcdd2c80f1e4fb6d09a3e2a607"
.metatheorem_resource_cache <- new.env(parent=emptyenv())
.metatheorem_review <- function() {
  path<-system.file("extdata","provability_representation.json",package="goedel")
  if(!nzchar(path)) .fail("Provability representation resource unavailable")
  resource_hash<-digest::digest(file=path,algo="sha256")
  if(!identical(resource_hash,.metatheorem_resource_cache$hash)) {
    .metatheorem_resource_cache$bundle<-jsonlite::fromJSON(path,simplifyVector=FALSE)
    .metatheorem_resource_cache$hash<-resource_hash
  }
  bundle<-.metatheorem_resource_cache$bundle
  refs<-bundle$resource_refs;expected<-c("pa_proof_representation.json","substitution_representation.json")
  bound<-.fields(refs,expected)&&all(vapply(expected,function(name) {
    target<-system.file("extdata",name,package="goedel")
    nzchar(target)&&identical(digest::digest(file=target,algo="sha256"),refs[[name]])
  },logical(1)))
  list(bundle=bundle,pinned=identical(resource_hash,.metatheorem_resource_sha)&&bound)
}
#' Check Conditional Metatheorem Applicability for the Exact PA Predicate
#'
#' Independently reviewed representation and Hilbert-Bernays-Loeb conditions are
#' bound to the exact installed predicate identity and resource digest. Declared
#' consistency, soundness and standard-model conditions remain assumptions. User
#' HBL flags cannot replace the review. A different predicate identity produces
#' UNKNOWN, never automatic transfer of these representation-specific results.
#' False structural declarations conflicting with reviewed properties produce
#' INCONSISTENT_CONTEXT. A false mathematical hypothesis yields NOT_APPLICABLE.
#' ESTABLISHED means conditional applicability, not a formal proof of the theorem
#' or a certification of any consistency or soundness assumption.
#' @param id A named catalogue statement identifier.
#' @param assumptions A named list of boolean mathematical declarations.
#' @param identity An optional exact predicate identity record. NULL selects the
#' concrete installed PA predicate.
#' @return A catalogue-inference result with separate D1, D2 and D3 review states.
#' @export
check_metatheorem <- function(id,assumptions,identity=NULL) {
  record<-lookup_statement(id);declared<-theory_context("PA",assumptions)$assumptions
  if(!is.null(identity)&&(!is.list(identity)||(length(identity)&&is.null(names(identity))))) .fail("Predicate identity must be an explicit record or NULL")
  builtin<-provability_identity();supplied<-if(is.null(identity))builtin else identity
  if(!length(supplied))supplied<-.empty_object()
  review<-.metatheorem_review();bundle<-review$bundle
  matched<-.inference_equal(supplied,builtin)&&.inference_equal(bundle$identity,builtin)
  proof_review<-bundle$proof_review;if(is.null(proof_review))proof_review<-bundle$review
  reviewed<-review$pinned&&matched&&identical(proof_review$status,"INDEPENDENTLY_CHECKED")
  hbl<-bundle$hbl_review
  states<-setNames(lapply(c("D1","D2","D3"),function(name) {
    if(reviewed&&identical(hbl$status,"INDEPENDENTLY_CHECKED")&&.inference_equal(hbl$predicate_identity,builtin)&&
       identical(hbl$conditions[[name]]$status,"INDEPENDENTLY_CHECKED"))"REVIEWED" else "OPEN"
  }),c("D1","D2","D3"))
  structural<-c("classical_first_order","decidable_axiom_set","diagonal_lemma_available","effective_axiomatized",
                "effective_language","extends_pa","provability_predicate_fixed","standard_arithmetization")
  known<-if(reviewed)setNames(as.list(rep(TRUE,length(structural))),structural)else list()
  for(name in names(states))if(states[[name]]=="REVIEWED")known[[name]]<-TRUE
  if(all(unlist(states,use.names=FALSE)=="REVIEWED"))known[["hbl_conditions"]]<-TRUE
  conflicts<-.sorted(names(known)[vapply(names(known),function(name)identical(declared[[name]],FALSE),logical(1))])
  effective<-declared
  for(name in c("hbl_conditions","provability_predicate_fixed","D1","D2","D3"))effective[[name]]<-NULL
  for(name in names(known))effective[[name]]<-known[[name]]
  required<-.sorted(unlist(record$requirements,use.names=FALSE))
  missing<-setdiff(required,names(effective))
  violated<-required[vapply(required,function(name)identical(effective[[name]],FALSE),logical(1))]
  if("hbl_conditions" %in% required)missing<-union(missing,names(states)[unlist(states,use.names=FALSE)=="OPEN"])
  inconsistent<-length(conflicts)>0L||(identical(declared[["consistent"]],FALSE)&&
    (identical(declared[["omega_consistent"]],TRUE)||identical(declared[["sigma1_sound"]],TRUE)))
  evidence<-record$evidence
  statement_reviewed<-identical(evidence$kind,"LITERATURE_RESULT")&&identical(evidence$review_status,"REVIEWED")&&
    evidence$verification_status %in% c("INDEPENDENTLY_CHECKED","FORMALLY_VERIFIED")
  status<-if(inconsistent)"INCONSISTENT_CONTEXT" else if(!matched||!reviewed||!statement_reviewed)"UNKNOWN" else if(length(violated))"NOT_APPLICABLE" else if(length(missing))"UNKNOWN" else "ESTABLISHED"
  repstatus<-if(reviewed)"INDEPENDENTLY_CHECKED"else"PENDING"
  theory<-supplied[["theory_id"]];if(is.null(theory))theory<-"UNSPECIFIED"
  .result(status,"CATALOGUE_INFERENCE",paste0("Conditional metatheorem applicability: ",id),declared,
    list(evidence,list(kind="REPRESENTATION_REVIEW",status=repstatus,predicate_identity=supplied)),
    c(unlist(record$limitations,use.names=FALSE),"Applicability is conditional on user declarations; no consistency or soundness assumption is proved."),
    details=list(statement_id=id,identity_status=if(matched)"MATCH"else"UNREVIEWED_IDENTITY",
      missing_requirements=as.list(.sorted(missing)),violated_requirements=as.list(.sorted(union(violated,conflicts))),
      representation_review=repstatus,hbl_conditions=states),
    context=list(theory_id=theory,metatheory_id="ordinary_classical_metamathematics",level="META",predicate_identity=supplied),
    dependencies=as.list(required))
}

#' Construct the Actual Conditional Goedel Sentence for the Fixed PA Predicate
#'
#' Applies the concrete fixed-point construction to the arithmetic formula
#' not Pr_PA(x). The result retains its displayed trusted representation premise
#' and native checked derivation of the conditional equivalence. It does not
#' assert the sentence's truth, unprovability or any theory's consistency.
#' Exact construction can require millions of decimal digits and substantial
#' resources; operational DAG and coding limits remain explicit.
#' @return A symbolic-construction result as returned by \code{fixed_point}.
#' @export
godel_sentence <- function() fixed_point(.dag_combine("not",list(provability_formula())))
