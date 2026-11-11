test_that("predicate review cannot transfer to a different theory", {
  flags<-list(classical_first_order=TRUE,consistent=TRUE,diagonal_lemma_available=TRUE,
    extends_pa=TRUE,hbl_conditions=TRUE,provability_predicate_fixed=TRUE)
  identity<-provability_identity()
  pa<-inference_context("PA",flags,predicate_identity=identity)
  extension<-inference_context("PA_plus_ConPA",flags,predicate_identity=identity)
  expect_identical(infer("proves_own_consistency",FALSE,pa)$status,"ESTABLISHED")
  expect_identical(infer("proves_own_consistency",FALSE,extension)$status,"UNKNOWN")
})

test_that("withdrawn evidence invalidates new and previously recorded inference", {
  flags<-list(classical_first_order=TRUE,consistent=TRUE,extends_pa=TRUE,
    decidable_axiom_set=TRUE,standard_arithmetization=TRUE)
  context<-inference_context("T",flags)
  witness<-infer("syntactically_complete",FALSE,context)$witness
  for(mutation in c("source_only_rule","draft_statement","missing_statement","new_requirement")) {
    local<-new.env(parent=environment(infer))
    for(name in c("infer","list_inference_rules","check_derivation",".inference_usable")) {
      fn<-get(name,envir=environment(infer));environment(fn)<-local;assign(name,fn,envir=local)
    }
    resource<-goedel:::.inference_rules();catalogue<-goedel:::.catalogue()
    if(mutation=="source_only_rule")for(i in seq_along(resource$data$rules))resource$data$rules[[i]]$verification_status<-"SOURCE_CHECKED"
    else if(mutation=="missing_statement")catalogue$statements<-Filter(function(s)s$id!="rosser",catalogue$statements)
    else for(i in seq_along(catalogue$statements))if(catalogue$statements[[i]]$id=="rosser") {
      if(mutation=="draft_statement")catalogue$statements[[i]]$evidence$review_status<-"DRAFT"
      else catalogue$statements[[i]]$requirements<-c(catalogue$statements[[i]]$requirements,list("additional_unsupported_hypothesis"))
    }
    local$.inference_rules<-function()resource;local$.catalogue<-function()catalogue
    expect_identical(local$infer("syntactically_complete",FALSE,context)$status,"UNKNOWN",info=mutation)
    expect_identical(local$check_derivation(witness)$status,"REFUTED",info=mutation)
  }
})

test_that("declarations stay conditional and identities replay", {
  context<-inference_context("T",list(consistent=TRUE))
  result<-infer("consistent",TRUE,context)
  expect_equal(result$status,"ESTABLISHED")
  expect_equal(result$mode,"CATALOGUE_INFERENCE")
  expect_equal(result$dependencies,list(list(property="consistent",value=TRUE,source="DECLARED_NOT_VERIFIED")))
  expect_equal(check_derivation(result$witness)$status,"ESTABLISHED")
  expect_equal(explain_derivation(result$witness)[[1]]$explanation,"User declaration; not independently verified.")
  other<-inference_context("Other",list(consistent=TRUE))
  expect_equal(check_derivation(result$witness,other)$status,"REFUTED")
})

test_that("semantic derivation mutations are rejected", {
  original<-infer("consistent",TRUE,inference_context("T",list(consistent=TRUE)))$witness
  for(mutation in c("theory","metatheory","level","polarity","undeclared","catalogue","rules","forward")) {
    witness<-original
    if(mutation=="theory")witness$steps[[1]]$fact$theory_id<-"Other"
    else if(mutation=="metatheory")witness$steps[[1]]$fact$metatheory_id<-"Other"
    else if(mutation=="level")witness$steps[[1]]$fact$level<-"OBJECT"
    else if(mutation=="polarity")witness$steps[[1]]$fact$value<-FALSE
    else if(mutation=="undeclared")witness$steps[[1]]$fact$property<-"omega_consistent"
    else if(mutation=="catalogue")witness$catalogue_sha256<-paste(rep("0",64),collapse="")
    else if(mutation=="rules")witness$rules_sha256<-paste(rep("0",64),collapse="")
    else witness$steps[[1]]$premises<-list(1L)
    expect_equal(check_derivation(witness)$status,"REFUTED",info=mutation)
    expect_error(explain_derivation(witness),class="goedel_error")
  }
})

test_that("finite inference failure and review absence remain UNKNOWN", {
  context<-inference_context("T",list(consistent=TRUE))
  expect_equal(infer("omega_consistent",TRUE,context)$status,"UNKNOWN")
  expect_equal(infer("consistent",TRUE,inference_context("T"))$status,"UNKNOWN")
  context<-inference_context("T",list(classical_first_order=TRUE,consistent=TRUE,
    diagonal_lemma_available=TRUE,extends_pa=TRUE,hbl_conditions=TRUE,provability_predicate_fixed=TRUE))
  expect_equal(infer("proves_own_consistency",FALSE,context)$status,"UNKNOWN")
})

test_that("inventory and typed graphs preserve provenance", {
  expect_length(catalogue_topics(),12L)
  expect_true(length(list_inference_rules())>=5L)
  ids<-vapply(search_catalogue("Con_Pr"),function(r)r$id,"")
  expect_true("consistency_formula" %in% ids)
  expect_equal(search_catalogue("CON_PR"),search_catalogue("con_pr"))
  expect_true(all(vapply(search_catalogue("",topic="metatheory"),function(r)"metatheory" %in% unlist(r$topic_ids),logical(1))))
  expect_error(search_catalogue("",topic="bogus"),class="goedel_error")
  graph<-catalogue_graph()
  kinds<-vapply(graph$edges,function(e)e$kind,"")
  expect_true(all(c("REQUIRES","RULE_PREMISE","RULE_CONCLUSION") %in% kinds))
  expect_equal(length(unique(vapply(graph$nodes,function(n)n$id,""))),length(graph$nodes))
  if(requireNamespace("igraph",quietly=TRUE)) {
    converted<-catalogue_graph("igraph")
    expect_s3_class(converted,"igraph")
    expect_equal(igraph::vcount(converted),length(graph$nodes))
    restored<-jsonlite::fromJSON(igraph::graph_attr(converted,"goedel_data"),simplifyVector=FALSE)
    expect_equal(restored,graph)
  }
})

test_that("reviewed three-step chains preserve hypothesis and polarity", {
  flags<-list(classical_first_order=TRUE,extends_pa=TRUE,omega_consistent=TRUE,
    decidable_axiom_set=TRUE,standard_arithmetization=TRUE)
  context<-inference_context("T",flags)
  result<-infer("syntactically_complete",FALSE,context)
  expect_equal(result$status,"ESTABLISHED")
  rules<-vapply(Filter(function(s)s$source=="RULE",result$witness$steps),function(s)s$rule,"")
  expect_equal(rules,c("omega_to_sigma1","sigma1_to_consistent","rosser_incomplete"))
  expect_equal(check_derivation(result$witness,context)$status,"ESTABLISHED")
  expect_equal(infer("syntactically_complete",TRUE,context)$status,"UNKNOWN")
  altered<-result$witness
  altered$steps[[length(altered$steps)]]$fact$value<-TRUE
  expect_equal(check_derivation(altered)$status,"REFUTED")
  flags$consistent<-FALSE
  expect_equal(infer("syntactically_complete",FALSE,inference_context("T",flags))$status,"INCONSISTENT_CONTEXT")
  context<-inference_context("T",list(classical_first_order=TRUE,extends_pa=TRUE,omega_consistent=TRUE))
  result<-infer("consistent",TRUE,context)
  altered<-result$witness
  endpoint<-length(altered$steps)
  altered$steps[[endpoint]]$premises<-head(altered$steps[[endpoint]]$premises,-1L)
  expect_equal(check_derivation(altered)$status,"REFUTED")
  expect_equal(infer("consistent",TRUE,context,max_steps=3L)$status,"UNKNOWN")
})
