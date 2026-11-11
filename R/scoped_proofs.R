#' Check Natural Deduction with Explicit Scopes and Discharge
#'
#' Each step has rule, formula, premises and scope. Premise and scope indices are
#' one-based. An assume step pushes its own index on the scope stack. Discharge
#' rules imp_intro, not_intro, classical and exists_elim close exactly the last
#' open assumption, specified by a singleton discharge list; their scope is the
#' remaining parent stack. Closed scopes cannot be reopened or referenced.
#' Ordinary premises must be accessible from the current scope. The final scope
#' must be empty. The calculus includes propositional connectives, falsity,
#' quantifiers and equality. or_elim takes A or B, A implies C and B implies C.
#' eq_elim takes equality s=t and a premise template[x:=s], with additional fields
#' template and variable; it concludes template[x:=t]. Quantifier elimination and
#' existential introduction have a term field. exists_elim has an eigenvariable
#' field variable and checks freshness against the existential, conclusion and
#' every undischarged assumption. Universal introduction checks every assumption.
#' The classical rule is enabled only in classical logic. This finite native
#' checker is not a formally verified kernel; assumptions and axioms are trusted.
#' @param steps An unnamed list of at most 4096 step records.
#' @param assumptions An unnamed list of global assumptions.
#' @param axioms An unnamed list of explicit trusted closed axioms.
#' @param theory Optional Q or PA descriptor for decidable axiom membership.
#' @param conclusion Optional required final formula.
#' @param logic Either classical or intuitionistic.
#' @return A checked-derivation result for the submitted proof's validity.
#' @examples
#' a <- predicate("A")
#' steps <- list(list(rule="assume", formula=a, premises=list(), scope=list(1L)),
#'   list(rule="imp_intro", formula=implication(a,a), premises=list(1L),
#'        scope=list(), discharge=list(1L)))
#' check_scoped_proof(steps)$status
#' @export
check_scoped_proof <- function(steps,assumptions=list(),axioms=list(),theory=NULL,conclusion=NULL,logic="classical") {
  .formula_list(assumptions,"assumptions");.formula_list(axioms,"axioms")
  if(any(vapply(axioms,function(x)length(free_variables(x))>0L,logical(1)))) .fail("Axioms must be closed")
  if(!is.null(theory)) .validate_theory(theory)
  if(!is.null(conclusion)) .require_formula(conclusion)
  if(!.scalar_string(logic)||!logic %in% c("classical","intuitionistic")) .fail("Invalid proof logic")
  .array(steps,"steps");if(length(steps)>4096L) .fail("Proof exceeds 4096 steps","RESOURCE_LIMIT")
  rules<-c("assume","assumption","axiom","reiterate","mp","and_intro","and_left","and_right","or_left","or_right","or_elim","false_elim","not_elim","imp_intro","not_intro","classical","exists_elim","forall_elim","exists_intro","forall_intro","eq_refl","eq_symm","eq_trans","eq_elim")
  closing<-c("imp_intro","not_intro","classical","exists_elim")
  indices<-function(xs) {
    .array(xs,"indices")
    for(x in xs)if(!is.numeric(x)||is.logical(x)||length(x)!=1L||is.na(x)||!is.finite(x)||x!=floor(x)) .fail("Indices must be integers")
  }
  exprs<-c(assumptions,axioms,if(!is.null(conclusion))list(conclusion))
  if(!is.null(theory))exprs<-c(exprs,theory$axioms,theory$extensions)
  for(s in steps) {
    if(!is.list(s)||!.scalar_string(s[["rule"]])||!s[["rule"]] %in% rules) .fail("Invalid scoped rule")
    fields<-c("rule","formula","premises","scope",if(s$rule %in% closing)"discharge",if(s$rule %in% c("forall_elim","exists_intro"))"term",if(s$rule %in% c("exists_elim","eq_elim"))"variable",if(s$rule=="eq_elim")"template")
    if(!.fields(s,fields)) .fail("Unrecognized or missing scoped step fields")
    .require_formula(s$formula);indices(s$premises);indices(s$scope);exprs<-c(exprs,list(s$formula))
    if(s$rule %in% closing)indices(s$discharge)
    if(s$rule %in% c("forall_elim","exists_intro")){.require_term(s$term);exprs<-c(exprs,list(s$term))}
    if(s$rule %in% c("exists_elim","eq_elim")&&! .name_ok(s$variable)) .fail("Invalid eigen/substitution variable")
    if(s$rule=="eq_elim"){.require_formula(s$template);exprs<-c(exprs,list(s$template))}
  }
  .joint_signature(exprs)
  scope<-integer();closed<-integer();supports<-list()
  result<-function(status,witness=NULL,invalid_step=NULL,reason="VALID") .result(status,"CHECKED_DERIVATION","validity_of_submitted_scoped_proof",assumptions,
    evidence=list(list(kind="NATIVE_RULE_CHECK",calculus="goedel-nd-scoped-v1",axioms=axioms,theory=theory)),
    limitations="Declared assumptions, closed axioms and the selected theory presentation are trusted; this native checker is not a formally verified kernel.",witness=witness,
    details=list(invalid_step=invalid_step,reason=reason,steps_checked=length(supports),open_scopes=as.list(scope)),context=list(logic=logic),
    dependencies=lapply(seq_along(supports),function(i)list(step=i,local_assumptions=as.list(supports[[i]]))))
  if(!length(steps))return(result("REFUTED",reason="EMPTY_PROOF"))
  vec<-function(x)as.integer(unlist(x,use.names=FALSE))
  same<-function(x,y)identical(vec(x),as.integer(y))
  prefix<-function(x,y)length(x)<=length(y)&&identical(as.integer(x),as.integer(head(y,length(x))))
  accessible<-function(j,target)prefix(vec(steps[[j]]$scope),target)&&!any(vec(steps[[j]]$scope) %in% closed)
  matches<-function(f,xs)any(vapply(xs,function(x)alpha_equal(f,x),logical(1)))
  for(i in seq_along(steps)) {
    s<-steps[[i]];f<-s$formula;r<-s$rule;refs<-vec(s$premises);ss<-vec(s$scope)
    arity<-switch(r,assume=0L,assumption=0L,axiom=0L,eq_refl=0L,mp=2L,and_intro=2L,or_elim=3L,not_elim=2L,exists_elim=2L,eq_trans=2L,eq_elim=2L,1L)
    valid<-length(refs)==arity&&all(refs>=1L&refs<i)
    next_scope<-scope
    if(valid&&r=="assume") {
      valid<-identical(ss,c(scope,as.integer(i)));next_scope<-ss
    } else if(valid&&r %in% closing) {
      valid<-length(scope)>0L&&same(s$discharge,tail(scope,1L))&&identical(ss,head(scope,-1L))
      if(valid) {
        endpoint<-tail(refs,1L);valid<-same(steps[[endpoint]]$scope,scope)&&!any(scope %in% closed)
        if(valid&&r=="exists_elim")valid<-accessible(refs[[1L]],ss)
        next_scope<-ss
      }
    } else if(valid) valid<-identical(ss,scope)&&all(vapply(refs,accessible,logical(1),target=scope))
    if(valid) {
      fs<-lapply(refs,function(j)steps[[j]]$formula)
      opened<-if(length(scope))steps[[tail(scope,1L)]]$formula else NULL
      live_assumptions<-c(assumptions,lapply(if(r %in% closing)head(scope,-1L) else scope,function(j)steps[[j]]$formula))
      free_assumptions<-unique(unlist(lapply(live_assumptions,free_variables),use.names=FALSE))
      valid<-switch(r,
        assume=TRUE,assumption=matches(f,assumptions),axiom=matches(f,axioms)||(!is.null(theory)&&.arithmetic_ok(f)&&is_axiom(theory,f)),
        reiterate=alpha_equal(f,fs[[1L]]),
        mp=fs[[2L]]$kind=="implies"&&alpha_equal(fs[[1L]],fs[[2L]]$args[[1L]])&&alpha_equal(f,fs[[2L]]$args[[2L]]),
        and_intro=f$kind=="and"&&alpha_equal(f$args[[1L]],fs[[1L]])&&alpha_equal(f$args[[2L]],fs[[2L]]),
        and_left=fs[[1L]]$kind=="and"&&alpha_equal(f,fs[[1L]]$args[[1L]]),
        and_right=fs[[1L]]$kind=="and"&&alpha_equal(f,fs[[1L]]$args[[2L]]),
        or_left=f$kind=="or"&&alpha_equal(f$args[[1L]],fs[[1L]]),
        or_right=f$kind=="or"&&alpha_equal(f$args[[2L]],fs[[1L]]),
        or_elim=fs[[1L]]$kind=="or"&&fs[[2L]]$kind=="implies"&&fs[[3L]]$kind=="implies"&&alpha_equal(fs[[1L]]$args[[1L]],fs[[2L]]$args[[1L]])&&alpha_equal(fs[[1L]]$args[[2L]],fs[[3L]]$args[[1L]])&&alpha_equal(f,fs[[2L]]$args[[2L]])&&alpha_equal(f,fs[[3L]]$args[[2L]]),
        false_elim=fs[[1L]]$kind=="bottom",
        not_elim=f$kind=="bottom"&&fs[[2L]]$kind=="not"&&alpha_equal(fs[[1L]],fs[[2L]]$args[[1L]]),
        imp_intro=f$kind=="implies"&&alpha_equal(f$args[[1L]],opened)&&alpha_equal(f$args[[2L]],fs[[1L]]),
        not_intro=f$kind=="not"&&fs[[1L]]$kind=="bottom"&&alpha_equal(f$args[[1L]],opened),
        classical=logic=="classical"&&opened$kind=="not"&&fs[[1L]]$kind=="bottom"&&alpha_equal(f,opened$args[[1L]]),
        forall_elim=fs[[1L]]$kind=="forall"&&alpha_equal(f,substitute_formula(fs[[1L]]$args[[1L]],fs[[1L]]$name,s$term)),
        exists_intro=f$kind=="exists"&&alpha_equal(fs[[1L]],substitute_formula(f$args[[1L]],f$name,s$term)),
        forall_intro=f$kind=="forall"&&alpha_equal(f$args[[1L]],fs[[1L]])&&!f$name %in% free_assumptions,
        exists_elim=fs[[1L]]$kind=="exists"&&alpha_equal(f,fs[[2L]])&&alpha_equal(opened,substitute_formula(fs[[1L]]$args[[1L]],fs[[1L]]$name,variable(s$variable)))&&!s$variable %in% c(free_assumptions,free_variables(fs[[1L]]),free_variables(f)),
        eq_refl=f$kind=="eq"&&alpha_equal(f$args[[1L]],f$args[[2L]]),
        eq_symm=f$kind=="eq"&&fs[[1L]]$kind=="eq"&&alpha_equal(f$args[[1L]],fs[[1L]]$args[[2L]])&&alpha_equal(f$args[[2L]],fs[[1L]]$args[[1L]]),
        eq_trans=f$kind=="eq"&&fs[[1L]]$kind=="eq"&&fs[[2L]]$kind=="eq"&&alpha_equal(fs[[1L]]$args[[2L]],fs[[2L]]$args[[1L]])&&alpha_equal(f$args[[1L]],fs[[1L]]$args[[1L]])&&alpha_equal(f$args[[2L]],fs[[2L]]$args[[2L]]),
        eq_elim=fs[[1L]]$kind=="eq"&&alpha_equal(fs[[2L]],substitute_formula(s$template,s$variable,fs[[1L]]$args[[1L]]))&&alpha_equal(f,substitute_formula(s$template,s$variable,fs[[1L]]$args[[2L]])))
    }
    if(!valid)return(result("REFUTED",invalid_step=i,reason="RULE_MISMATCH"))
    support<-if(r=="assume")as.integer(i) else sort(unique(as.integer(unlist(supports[refs],use.names=FALSE))))
    if(r %in% closing)support<-setdiff(support,tail(scope,1L))
    supports[[length(supports)+1L]]<-support
    if(r %in% closing)closed<-c(closed,tail(scope,1L))
    scope<-next_scope
  }
  if(length(scope))return(result("REFUTED",invalid_step=length(steps),reason="UNCLOSED_SCOPE"))
  if(!is.null(conclusion)&&!alpha_equal(conclusion,tail(steps,1L)[[1L]]$formula))return(result("REFUTED",invalid_step=length(steps),reason="CONCLUSION_MISMATCH"))
  result("ESTABLISHED",witness=steps)
}
