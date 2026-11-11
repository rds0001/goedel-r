.pa_formula_cache <- new.env(parent=emptyenv())
.pa_identity_cache <- new.env(parent=emptyenv())
.pa_resource_cache <- new.env(parent=emptyenv())
#' Transport Finite Proofs in the Explicit Hilbert Presentation of PA
#'
#' Each step contains rule (a natural integer), formula (a natural syntax code),
#' aux_a and aux_b (natural decimal strings). The sequence envelope is
#' [20261106,1,N,rule,formula,aux_a,aux_b,0,0,...]. Reserved auxiliary fields are
#' zero. This format is distinct from the scoped JSON proof transport, even
#' though both use the natural-sequence codec. Structural decoding does not
#' establish proof validity; unknown natural rule numbers remain representable.
#' The runtime transport accepts 1 through 4096 steps. The mathematical Hilbert
#' proof relation is not restricted to that operational limit.
#' @param steps A nonempty list of Hilbert step records.
#' @param code A canonical natural decimal proof code.
#' @return An exact decimal proof code, or its structural step list.
#' @examples
#' steps <- list(list(rule=6L,formula="0",aux_a="0",aux_b="0"))
#' identical(pa_proof_decode(pa_proof_encode(steps)), steps)
#' @export
pa_proof_encode <- function(steps) {
  .array(steps,"steps");if(!length(steps)) .fail("A Hilbert proof must contain a step")
  if(length(steps)>4096L) .fail("Hilbert proof step budget exceeded","RESOURCE_LIMIT")
  cells<-vector("list",3L+6L*length(steps));cells[1:3]<-list("20261106","1",as.character(length(steps)))
  for(i in seq_along(steps)) {
    s<-steps[[i]]
    if(!.fields(s,c("rule","formula","aux_a","aux_b"))||!.register_integer(s$rule,0L,2147483647L)) .fail("Invalid Hilbert proof step")
    for(key in c("formula","aux_a","aux_b")) .big_nat(s[[key]],5000000L)
    cells[seq.int(6L*i-2L,6L*i+3L)]<-list(formatC(s$rule,format="f",digits=0),s$formula,s$aux_a,s$aux_b,"0","0")
  }
  sequence_encode(cells)
}
#' @rdname pa_proof_encode
#' @export
pa_proof_decode <- function(code) {
  cells<-sequence_decode(code,max_items=24579L)
  if(length(cells)<3L||cells[[1L]]!="20261106"||cells[[2L]]!="1") .fail("Unknown Hilbert proof numbering")
  n<-.big_nat(cells[[3L]])
  if(n<1L||n>4096L||length(cells)!=3L+6L*as.integer(n)) .fail("Invalid Hilbert proof length")
  steps<-vector("list",as.integer(n))
  for(i in seq_len(as.integer(n))) {
    row<-cells[seq.int(6L*i-2L,6L*i+3L)];rule<-.big_nat(row[[1L]])
    if(rule>2147483647L||row[[5L]]!="0"||row[[6L]]!="0") .fail("Invalid Hilbert rule or reserved fields")
    steps[[i]]<-list(rule=as.integer(rule),formula=row[[2L]],aux_a=row[[3L]],aux_b=row[[4L]])
  };steps
}
.pa_representation <- function() {
  path<-system.file("extdata","pa_proof_representation.json",package="goedel")
  if(!nzchar(path)) .fail("PA representation resource unavailable")
  resource_hash<-digest::digest(file=path,algo="sha256")
  if(identical(resource_hash,.pa_resource_cache$hash))return(.pa_resource_cache$bundle)
  bundle<-jsonlite::fromJSON(path,simplifyVector=FALSE);record<-bundle$representation;program<-bundle$program
  if(!is.list(bundle)||!identical(bundle$schema_version,"1.0")||!is.list(record)||!is.list(program)||!identical(program$id,"goedel-pa-hilbert-proof-v1")) .fail("Invalid PA representation envelope")
  .register_validate(program)
  if(!identical(.register_hash(program),record$program_sha256)||!identical(dag_fingerprint(record$arithmetic_dag),record$arithmetic_sha256)||!identical(record$inputs,list("x0","x1"))||!identical(record$output,"x2")) .fail("PA program and arithmetic representation mismatch")
  info<-validate_arithmetic_dag(record$arithmetic_dag)
  if(info$root_sort!="formula"||!identical(info$free_variables,list("x0","x1","x2"))) .fail("PA graph has unexpected free variables")
  .pa_resource_cache$hash<-resource_hash;.pa_resource_cache$bundle<-bundle
  bundle
}
#' Construct Predicate-Specific PA Provability and Consistency Formulas
#'
#' The concrete arithmetic graph represents the complete explicit Hilbert PA
#' checker, with output fixed to one. The existential proof-code quantifier yields
#' Pr_PA; its negation at the code of zero equals successor zero yields the
#' predicate-specific consistency formula. These are symbolic constructions, not
#' assertions of consistency, proof-assistant verification or derivability
#' conditions. Indexed variable substitution avoids capture, including when a
#' requested name occurs among compiler-generated binders. The Hilbert calculus
#' and its literal Q patterns are separate from the scoped natural-deduction API.
#' @param pvar,proofvar Indexed proof-code variable names.
#' @param xvar Indexed conclusion-code variable name, distinct from the proof variable.
#' @param index Q axiom index, an integer from 1 through 7.
#' @return Arithmetic formula DAGs, or exact predicate identity metadata.
#' @examples
#' axiom <- hilbert_q_axiom(4L)
#' validate_arithmetic_dag(axiom)$free_variables
#' @export
proof_PA_formula <- function(pvar="x0",xvar="x1") {
  if(!.dag_name(pvar)||!.dag_name(xvar)||pvar==xvar) .fail("Proof and conclusion require distinct indexed variables")
  record<-.pa_representation()$representation
  key<-list(program=record$program_sha256,graph=record$arithmetic_sha256,pvar=pvar,xvar=xvar)
  if(identical(key,.pa_formula_cache$key))return(.pa_formula_cache$graph)
  graph<-record$arithmetic_dag
  names_all<-vapply(graph$nodes,function(n)if(n$op %in% c("var","forall","exists"))n$name else "","")
  names_all<-.numeric_names(c(names_all[nzchar(names_all)],pvar,xvar));last<-.big_nat(substring(tail(names_all,1L),2L),4096L)
  ptmp<-paste0("x",as.character(last+1L));xtmp<-paste0("x",as.character(last+2L))
  replacements<-list(list("x0",.dag_atom("var",ptmp)),list("x1",.dag_atom("var",xtmp)),list("x2",.dag_atom("num","1")),list(ptmp,.dag_atom("var",pvar)),list(xtmp,.dag_atom("var",xvar)))
  for(pair in replacements)graph<-dag_substitute(graph,pair[[1L]],pair[[2L]])
  .pa_formula_cache$key<-key;.pa_formula_cache$graph<-graph
  graph
}
#' @rdname proof_PA_formula
#' @export
provability_formula <- function(xvar="x1",proofvar="x0") {
  graph<-proof_PA_formula(proofvar,xvar);n<-length(graph$nodes)
  if(n>=200000L) .fail("DAG node budget exceeded","RESOURCE_LIMIT")
  list(schema_version="1.0",nodes=c(graph$nodes,list(list(op="exists",name=proofvar,args=list(graph$root)))),root=n)
}
.pa_contradiction <- function() {
  b<-.dag_builder();z<-b$node("zero");s<-b$node("succ",args=list(z));b$export(b$node("eq",args=list(z,s)))
}
#' @rdname proof_PA_formula
#' @export
consistency_formula <- function() {
  code<-arithmetic_dag_encode(.pa_contradiction());formula<-dag_substitute(provability_formula(),"x1",.dag_atom("num",code))
  .dag_combine("not",list(formula))
}
#' @rdname proof_PA_formula
#' @export
provability_identity <- function() {
  record<-.pa_representation()$representation
  key<-list(program=record$program_sha256,graph=record$arithmetic_sha256)
  if(identical(key,.pa_identity_cache$key))return(.pa_identity_cache$identity)
  identity<-list(schema_version="1.0",theory_id="PA",theory_presentation="goedel-pa-hilbert-theory-v1",calculus_id="goedel-pa-hilbert-proof-v1",numbering_id="goedel-arithmetic-dag-v1",proof_numbering_id="goedel-pa-hilbert-proof-sequence-v1",program_sha256=record$program_sha256,graph_sha256=record$arithmetic_sha256,predicate_sha256=dag_fingerprint(provability_formula()),contradiction_code=arithmetic_dag_encode(.pa_contradiction()))
  .pa_identity_cache$key<-key;.pa_identity_cache$identity<-identity
  identity
}
.q_hilbert_codes <- c("500916525028717704190487132685665064192049151","34128533460435954929216433013749539833340190205358723760417406975","659269241530276489251887774916317243209608597141772127334720066388438037764767743","7303094192337005764632264550179605053439","2133033341277245731431407528563156690439727583356260119625072639","7303104576930742177100635445239058792447","8532133365108982925472268923064903045895990360676493062035210239")
#' @rdname proof_PA_formula
#' @export
hilbert_q_axiom <- function(index) {
  if(!.register_integer(index,1L,7L)) .fail("Q index must be an integer in 1..7")
  arithmetic_dag_decode(.q_hilbert_codes[[index]])
}
#' Check a Submitted Proof with the Complete Fixed PA Hilbert Program
#'
#' Executes the exact register program underlying the arithmetic predicate.
#' ESTABLISHED accepts this submitted finite derivation; REFUTED rejects it;
#' UNKNOWN records exhaustion of the declared step budget. No result establishes
#' PA's consistency or general unprovability. Context binds the exact program,
#' graph, predicate, calculus, theory and numbering identities.
#' @param proof_code A canonical natural decimal Hilbert proof code.
#' @param conclusion_code A canonical natural decimal arithmetic formula code.
#' @param max_steps An execution budget from 1 through 1000000 transitions.
#' @return A checked-derivation result with reason, steps used and exact identity.
#' @export
check_pa_proof <- function(proof_code,conclusion_code,max_steps=1000000L) {
  bundle<-.pa_representation();answer<-run_register_program(bundle$program,list(proof_code,conclusion_code),max_steps=max_steps)
  details<-answer$details
  if(!details$halted){status<-"UNKNOWN";reason<-"STEP_LIMIT"}
  else if(details$output=="1"){status<-"ESTABLISHED";reason<-"VALID"}
  else if(details$output=="0"){status<-"REFUTED";reason<-"INVALID_PROOF"}
  else .fail("PA checker returned a nonboolean result")
  identity<-provability_identity()
  .result(status,"CHECKED_DERIVATION","Validity of submitted PA Hilbert proof",evidence=list(list(kind="NATIVE_REGISTER_CHECK",program_sha256=identity$program_sha256)),
    limitations="This validates one submitted finite proof under the fixed PA calculus. It does not establish PA consistency; budget exhaustion is not unprovability.",
    details=list(reason=reason,steps_used=details$steps_used,halted=details$halted,output=details$output),context=identity)
}
