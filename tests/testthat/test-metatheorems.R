test_that("predicate-specific applications do not prove their assumptions", {
  second<-check_metatheorem("godel_second_hbl",list(consistent=TRUE))
  loeb<-check_metatheorem("lob",list())
  expect_identical(second$status,"ESTABLISHED")
  expect_identical(loeb$status,"ESTABLISHED")
  expect_identical(second$assumptions,list(consistent=TRUE))
  expect_identical(second$details$hbl_conditions,list(D1="REVIEWED",D2="REVIEWED",D3="REVIEWED"))
  expect_identical(check_metatheorem("godel_second_hbl",list())$status,"UNKNOWN")
  expect_identical(check_metatheorem("godel_second_hbl",list(consistent=FALSE))$status,"NOT_APPLICABLE")
  cases<-list(godel_first_consistency="consistent",godel_first_omega="omega_consistent",godel_first_sigma1="sigma1_sound",rosser="consistent",tarski="standard_naturals")
  for(id in names(cases)) {
    key<-cases[[id]];unknown<-check_metatheorem(id,list())
    expect_identical(unknown$status,"UNKNOWN")
    expect_true(key %in% unlist(unknown$details$missing_requirements))
    expect_identical(check_metatheorem(id,setNames(list(TRUE),key))$status,"ESTABLISHED")
  }
  for(flags in list(list(classical_first_order=FALSE),list(D2=FALSE),list(hbl_conditions=FALSE),list(consistent=FALSE,omega_consistent=TRUE)))
    expect_identical(check_metatheorem("lob",flags)$status,"INCONSISTENT_CONTEXT")
})
test_that("user flags and altered evidence never replace exact representation review", {
  identity<-provability_identity();identity$predicate_sha256<-strrep("0",64L)
  custom<-check_metatheorem("godel_second_hbl",list(consistent=TRUE,hbl_conditions=TRUE,D1=TRUE,D2=TRUE,D3=TRUE,provability_predicate_fixed=TRUE),identity)
  expect_identical(custom$status,"UNKNOWN")
  expect_identical(custom$details$identity_status,"UNREVIEWED_IDENTITY")
  expect_identical(custom$details$hbl_conditions$D2,"OPEN")
  original<-goedel:::.metatheorem_review()
  expect_true(original$pinned)
  for(mutation in c("missing_d2","wrong_predicate","source_only","unpinned")) {
    review<-original
    if(mutation=="missing_d2")review$bundle$hbl_review$conditions$D2<-NULL
    if(mutation=="wrong_predicate")review$bundle$hbl_review$predicate_identity$predicate_sha256<-strrep("0",64L)
    if(mutation=="source_only")review$bundle$hbl_review$conditions$D2$status<-"SOURCE_CHECKED"
    if(mutation=="unpinned")review$pinned<-FALSE
    fn<-check_metatheorem;environment(fn)<-new.env(parent=environment(check_metatheorem))
    environment(fn)$.metatheorem_review<-function()review
    answer<-fn("lob",list(hbl_conditions=TRUE,D2=TRUE))
    expect_identical(answer$status,"UNKNOWN")
    expect_true("D2" %in% unlist(answer$details$missing_requirements))
  }
  row<-lookup_statement("lob");row$evidence$kind<-"DEFINITION"
  fn<-check_metatheorem;environment(fn)<-new.env(parent=environment(check_metatheorem))
  environment(fn)$lookup_statement<-function(id)row
  expect_identical(fn("lob",list())$status,"UNKNOWN")
  expect_error(check_metatheorem("lob",list(),identity="PA"),class="goedel_error")
})
