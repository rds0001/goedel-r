test_that("numbering uses exact independently computed code", {
  expected <- "2877079724461132065077027294299967182165085032993045229375792477975649140191511716477"
  expect_identical(encode(variable("x")), expected)
  expect_identical(serialize_record(decode(expected)), '{"args":[],"kind":"var","name":"x"}')
  expect_true(nchar(expected) > 16L)
  expect_identical(numbering()$id, "goedel-json-byte-v1")
  expect_identical(nchar(fingerprint(variable("x"))), 64L)
  for (code in c("0", "01", "1", "2", "255", "-1", "1.5", "x")) expect_error(decode(code), class = "goedel_error")
  expect_error(decode(2^54), class = "goedel_error")
  expect_error(decode(paste(rep("1", 2501L), collapse = "")), class = "goedel_error")
  f <- predicate("P", rep(list(variable("x")), 40L))
  expect_error(encode(f), class = "goedel_error")
  for (f in list(variable("x"), predicate("P"), bottom(), forall("x", predicate("P", list(variable("x")))))) {
    expect_identical(serialize_record(decode(encode(f))), serialize_record(f))
  }
})
