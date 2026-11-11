# Inspect the actual source tree or source tarball before release.
args <- commandArgs(TRUE)
forbidden <- c("scaffold", "goedel-scaffold", "intern", "transformation", "archiv", "unterlagen", "downloads")
if (length(args)) {
  stopifnot(length(args) == 1L, file.exists(args[[1L]]))
  paths <- utils::untar(args[[1L]], list = TRUE)
} else {
  paths <- list.files(".", recursive = TRUE, all.files = TRUE, include.dirs = TRUE, no.. = TRUE)
  paths <- paths[!grepl("^\\.git(/|$)", paths)]
}
bad <- vapply(strsplit(tolower(paths), "/", fixed = TRUE), function(x) any(x %in% forbidden), logical(1)) |
  grepl("(^|/)(hosts\\.yml|credentials|\\.env)$|\\.(docx?|odt|zip)$", paths, ignore.case = TRUE)
if (any(bad)) stop("Forbidden package content: ", paste(paths[bad], collapse = ", "))
if (!length(args)) {
  approved <- c("catalogue.json", "reference_cases.json", "expr.schema.json", "catalogue_review.json",
    "inference_rules.json", "substitution_representation.json", "pa_proof_representation.json", "provability_representation.json",
    "pa_hbl_review.json", "pa_proof_review.json")
  actual <- list.files("inst/extdata", all.files = TRUE, no.. = TRUE)
  if (!setequal(actual, approved)) stop("Unexpected/missing installed resources")
  raw <- paste(readLines("inst/extdata/catalogue.json", warn = FALSE), collapse = "\n")
  if (grepl('"(private|never_publish)"\\s*:\\s*true|/mnt/|/home/', raw)) stop("Private catalogue content")
  invisible(jsonlite::fromJSON(raw, simplifyVector = FALSE))
  reproduction <- "inst/reproduction"
  manifest <- jsonlite::fromJSON(file.path(reproduction,"manifest.json"),simplifyVector=FALSE)
  expected <- names(manifest$files_sha256)
  if(any(!grepl("^[A-Za-z0-9_.-]+$",expected))||
     !setequal(list.files(reproduction,all.files=TRUE,no..=TRUE),c("manifest.json",expected)))
    stop("Unexpected scientific reproduction source files")
  for(name in expected)if(!identical(digest::digest(file=file.path(reproduction,name),algo="sha256"),manifest$files_sha256[[name]]))
    stop("Scientific reproduction source hash mismatch: ",name)
}
message("Publication boundary: PASS")
