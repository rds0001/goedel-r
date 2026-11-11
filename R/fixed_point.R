.dag_import <- function(builder,dag) {
  mapping<-integer(length(dag$nodes))
  for(i in seq_along(dag$nodes)){n<-dag$nodes[[i]];mapping[[i]]<-builder$node(n$op,n$name,lapply(n$args,function(a)mapping[[a+1L]]))}
  mapping[[dag$root+1L]]
}
.dag_combine <- function(op,dags=list(),name="") {
  b<-.dag_builder();args<-lapply(dags,function(d).dag_import(b,d));b$export(b$node(op,name,args))
}
.dag_atom <- function(op,name="")list(schema_version="1.0",nodes=list(list(op=op,name=name,args=list())),root=0L)
.dag_child <- function(dag,position) {
  i<-dag$nodes[[dag$root+1L]]$args[[position]]
  list(schema_version="1.0",nodes=dag$nodes[seq_len(i+1L)],root=i)
}
.substitution_bundle <- function() {
  path<-system.file("extdata","substitution_representation.json",package="goedel")
  if(!nzchar(path)) .fail("Substitution representation resource unavailable")
  jsonlite::fromJSON(path,simplifyVector=FALSE)
}
.validate_representation <- function(bundle) {
  if(!.fields(bundle,c("schema_version","program","representation","review"))||!identical(bundle$schema_version,"1.0")) .fail("Invalid substitution representation bundle")
  .register_validate(bundle$program);r<-bundle$representation
  if(!is.list(r)||!identical(r$program_id,"goedel-dag-closed-substitution-v1")||!identical(r$machine_id,"goedel-arithmetic-register-v1")||!identical(r$program_sha256,.register_hash(bundle$program))) .fail("Substitution program identity mismatch")
  if(!identical(r$inputs,list("x0","x1","x2"))||!identical(r$output,"x3")) .fail("Representation input/output mismatch")
  info<-.dag_info(r$arithmetic_dag)
  if(info$statistics$root_sort!="formula"||!identical(info$statistics$free_variables,list("x0","x1","x2","x3"))) .fail("Unexpected representation free variables")
  if(!identical(r$arithmetic_sha256,dag_fingerprint(r$arithmetic_dag))) .fail("Arithmetic representation hash mismatch")
  if(!identical(r$bounded_sha256,dag_fingerprint(r$bounded_dag,TRUE))) .fail("Bounded representation hash mismatch")
  for(key in c("program_sha256","arithmetic_sha256","bounded_sha256"))if(!identical(bundle$review[[key]],r[[key]])) .fail("Representation review binding changed")
  invisible(TRUE)
}
#' Construct a Concrete Arithmetic Fixed Point with a Checked Logical Bridge
#'
#' Builds the actual arithmetic substitution graph from the packaged reviewed
#' register-program compilation. No opaque substitution predicate is inserted.
#' The diagonal formula and its exact presentation-sensitive codes are retained.
#' A twenty-step native first-order derivation checks the fixed-point equivalence
#' conditional on the displayed numeralwise representation premise. The checker
#' does not prove that premise. Independent mathematical review supports the
#' built-in correspondence; an unrecognized explicit bundle remains UNKNOWN.
#' No result asserts the sentence's truth, unprovability or consistency.
#' @param phi An arithmetic formula DAG with exactly one free indexed variable.
#' @param representation Optional explicit substitution representation bundle.
#' @return A symbolic-construction result with the concrete sentence G, codes q
#' and m, representation premise, logical derivation and independent replay result.
#' @export
fixed_point <- function(phi,representation=NULL) {
  info<-.dag_info(phi)
  if(info$statistics$root_sort!="formula"||length(info$statistics$free_variables)!=1L) .fail("Fixed point requires a formula with exactly one free variable")
  bundle<-if(is.null(representation)).substitution_bundle() else representation
  .validate_representation(bundle);sub<-bundle$representation$arithmetic_dag
  reviewed<-identical(.register_hash(bundle),"09ed7e7edbaf7f775e7d320c2ef20488705c8312cc45217c460f1fc914f12ef6")&&identical(bundle$review$status,"INDEPENDENTLY_CHECKED")&&identical(bundle$review$formal_kernel,FALSE)
  names_all<-vapply(c(phi$nodes,sub$nodes),function(n)if(n$op %in% c("var","forall","exists"))n$name else "","")
  names_all<-.numeric_names(names_all[nzchar(names_all)]);last<-.big_nat(substring(tail(names_all,1L),2L),4096L)
  x<-paste0("x",as.character(last+1L));z<-paste0("x",as.character(last+2L));input<-info$statistics$free_variables[[1L]]
  xt<-.dag_atom("var",x);zt<-.dag_atom("var",z);it<-.dag_atom("num",substring(x,2L))
  sub_x<-dag_substitute(sub,"x0",xt);sub_x<-dag_substitute(sub_x,"x1",it);sub_x<-dag_substitute(sub_x,"x2",xt);sub_x<-dag_substitute(sub_x,"x3",zt)
  pz<-dag_substitute(phi,input,zt)
  implication_dag<-function(a,b).dag_combine("implies",list(a,b))
  universal<-function(v,f).dag_combine("forall",list(f),v)
  delta<-universal(z,implication_dag(sub_x,pz));q<-arithmetic_dag_encode(delta)
  G<-dag_substitute_numeral(delta,x,q);m<-arithmetic_dag_encode(G)
  equation_checked<-identical(substitute_code(q,substring(x,2L),q),m)
  if(!equation_checked) .fail("Fixed-point code equation failed")
  mt<-.dag_atom("num",m);pm<-dag_substitute(phi,input,mt)
  sz<-dag_substitute(sub_x,x,.dag_atom("num",q));sm<-dag_substitute(sz,z,mt)
  arena<-.dag_builder();roots<-lapply(list(zt,mt,sz,sm,pz,pm,G),function(d).dag_import(arena,d))
  zr<-roots[[1L]];mr<-roots[[2L]];szr<-roots[[3L]];smr<-roots[[4L]];pzr<-roots[[5L]];pmr<-roots[[6L]];gr<-roots[[7L]]
  binary<-function(op,a,b)arena$node(op,args=list(a,b))
  iff_root<-function(a,b){ab<-binary("implies",a,b);ba<-binary("implies",b,a);binary("and",ab,ba)}
  equality<-binary("eq",zr,mr);premise_root<-arena$node("forall",z,list(iff_root(szr,equality)));target_root<-iff_root(gr,pmr)
  premise<-arena$export(premise_root);target<-arena$export(target_root)
  steps<-list();step<-function(rule,root,premises=list(),scope=list(),...){steps[[length(steps)+1L]]<<-c(list(rule=rule,formula=arena$export(root),premises=premises,scope=scope),list(...))}
  equal_mm<-binary("eq",mr,mr)
  step("axiom",premise_root)
  step("assume",gr,scope=list(2L))
  step("forall_elim",iff_root(smr,equal_mm),list(1L),list(2L),term=mt)
  step("and_right",binary("implies",equal_mm,smr),list(3L),list(2L))
  step("eq_refl",equal_mm,scope=list(2L))
  step("mp",smr,list(5L,4L),list(2L))
  step("forall_elim",binary("implies",smr,pmr),list(2L),list(2L),term=mt)
  step("mp",pmr,list(6L,7L),list(2L))
  step("imp_intro",binary("implies",gr,pmr),list(8L),discharge=list(2L))
  step("assume",pmr,scope=list(10L))
  step("assume",szr,scope=list(10L,11L))
  step("forall_elim",iff_root(szr,equality),list(1L),list(10L,11L),term=zt)
  step("and_left",binary("implies",szr,equality),list(12L),list(10L,11L))
  step("mp",equality,list(11L,13L),list(10L,11L))
  step("eq_symm",binary("eq",mr,zr),list(14L),list(10L,11L))
  step("eq_elim",pzr,list(15L,10L),list(10L,11L),template=pz,variable=z)
  step("imp_intro",binary("implies",szr,pzr),list(16L),list(10L),discharge=list(11L))
  step("forall_intro",gr,list(17L),list(10L))
  step("imp_intro",binary("implies",pmr,gr),list(18L),discharge=list(10L))
  step("and_intro",target_root,list(9L,19L))
  checked<-check_scoped_dag_proof(steps,axioms=list(premise),conclusion=target)
  valid<-checked$status=="ESTABLISHED"
  .result(if(reviewed&&valid)"ESTABLISHED" else "UNKNOWN","SYMBOLIC_CONSTRUCTION","Conditional fixed-point equivalence under the displayed representation premise",
    assumptions=list(list(kind="REPRESENTATION_INSTANCE",formula=premise,proved_by_native_checker=FALSE)),evidence=list(bundle$review),
    limitations=c("The representation premise is supported by independent mathematical review, not proved by the native deduction checker.","The constructed sentence is not thereby asserted true, unprovable, or a consistency statement."),
    witness=list(phi=phi,delta=delta,G=G,q=q,m=m,variable=input,diagonal_variable=x,output_variable=z,numbering_id="goedel-arithmetic-dag-v1",program_sha256=bundle$representation$program_sha256,arithmetic_sha256=bundle$representation$arithmetic_sha256,representation_instance=premise,target=target,derivation=steps,checked_proof=checked,trusted_premises=list(premise)),
    details=list(representation_reviewed=reviewed,code_equation_checked=equation_checked,native_derivation_checked=valid,formal_kernel_replay=FALSE),
    context=list(theory="PA",numbering="goedel-arithmetic-dag-v1",representation_id="goedel-dag-closed-substitution-v1"),
    dependencies=list(list(program_sha256=bundle$representation$program_sha256,arithmetic_sha256=bundle$representation$arithmetic_sha256)))
}
