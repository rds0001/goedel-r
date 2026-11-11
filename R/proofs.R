.empty_object <- function() structure(list(), names = character())
.result <- function(status, mode, claim, assumptions = list(), evidence = list(),
                    limitations = character(), witness = NULL, details = .empty_object(),
                    context = .empty_object(), dependencies = list()) {
  structure(list(status = status, mode = mode, claim = claim, context = context,
    assumptions = assumptions, evidence = evidence, dependencies = dependencies,
    limitations = as.list(limitations), witness = witness, details = details), class = "goedel_result")
}
.formula_list <- function(xs, label) {
  if (!is.list(xs) || !is.null(names(xs))) .fail(paste(label, "must be an array"))
  if (length(xs) > 1000L) .fail(paste(label, "exceeds 1000 entries"), "RESOURCE_LIMIT")
  for (x in xs) .require_formula(x)
  invisible(xs)
}
.joint_signature <- function(expressions) {
  arities <- new.env(parent = emptyenv())
  walk <- function(x) {
    if (x$kind %in% c("func", "pred")) {
      key <- paste(x$kind, x$name, sep = ":"); arity <- length(x$args)
      if (exists(key, arities, inherits = FALSE) && get(key, arities) != arity) .fail("Inconsistent joint symbol arity")
      assign(key, arity, envir = arities)
    }
    for (a in x$args) walk(a)
  }
  for (x in expressions) walk(x)
  invisible(TRUE)
}
.proof_result <- function(status, assumptions, axioms, witness = NULL,
                          invalid_step = NULL, reason = "VALID") {
  .result(status, "CHECKED_DERIVATION", "validity_of_submitted_proof", assumptions,
    list(list(kind = "NATIVE_RULE_CHECK", calculus = "goedel-nd-fragment-v1", axioms = axioms)),
    "Assumptions and closed axioms are trusted; the checker is not a formally verified kernel.",
    witness, list(invalid_step = invalid_step, reason = reason))
}

#' Check an Explicit Finite Derivation
#'
#' Checks the natural-deduction fragment \code{goedel-nd-fragment-v1}. Supported
#' rules are assumption, axiom, mp, and_intro, and_left, and_right, forall_elim
#' and forall_intro. Premise indices are one-based and refer only to earlier
#' steps. The first premise of mp is the antecedent and the second an implication.
#' Universal introduction checks all declared assumptions for the eigenvariable
#' condition. Axioms must be closed and are explicitly trusted. Each step has
#' exactly rule, formula and premises; forall_elim additionally has term.
#' There are at most 256 steps. Malformed payloads raise \code{goedel_error};
#' invalid rule applications return REFUTED about this proof's validity, never
#' about the truth of the submitted conclusion. This native checker is not a
#' formally verified proof assistant and has no completeness claim.
#' @param steps An unnamed list of step lists.
#' @param assumptions An unnamed list of formulas trusted as assumptions.
#' @param axioms An unnamed list of trusted closed formulas.
#' @param conclusion Optional expected final formula.
#' @return A \code{goedel_result} with status, mode, claim, context, assumptions,
#' evidence, dependencies, limitations, witness and details. A successful witness
#' is the checked step list; failure details identify the invalid step and reason.
#' @examples
#' a <- predicate("A")
#' b <- predicate("B")
#' premises <- list(a, implication(a, b))
#' steps <- list(list(rule = "assumption", formula = a, premises = list()),
#'   list(rule = "assumption", formula = implication(a, b), premises = list()),
#'   list(rule = "mp", formula = b, premises = list(1L, 2L)))
#' check_proof(steps, premises, conclusion = b)$status
#' @export
check_proof <- function(steps, assumptions = list(), axioms = list(), conclusion = NULL) {
  .formula_list(assumptions, "assumptions"); .formula_list(axioms, "axioms")
  if (any(vapply(axioms, function(x) length(free_variables(x)) > 0L, logical(1)))) .fail("Axioms must be closed")
  if (!is.null(conclusion)) .require_formula(conclusion)
  if (!is.list(steps) || !is.null(names(steps))) .fail("steps must be an array")
  if (length(steps) > 256L) .fail("Proof exceeds 256 steps", "RESOURCE_LIMIT")
  if (!length(steps)) return(.proof_result("REFUTED", assumptions, axioms, reason = "EMPTY_PROOF"))
  rules <- c("assumption", "axiom", "mp", "and_intro", "and_left", "and_right", "forall_elim", "forall_intro")
  # Validate the entire payload before testing inference rules.
  for (i in seq_along(steps)) {
    step <- steps[[i]]
    if (!is.list(step) || anyDuplicated(names(step)) || !.scalar_string(step$rule) || !step$rule %in% rules) .fail("Invalid proof step/rule")
    fields <- c("rule", "formula", "premises", if (step$rule == "forall_elim") "term")
    if (length(step) != length(fields) || !setequal(names(step), fields)) .fail("Unrecognized/missing step fields")
    .require_formula(step$formula)
    refs <- step$premises
    if (!is.list(refs) || !is.null(names(refs))) .fail("premises must be an array")
    for (ref in refs) if (!is.numeric(ref) || is.logical(ref) || length(ref) != 1L ||
      is.na(ref) || !is.finite(ref) || ref != floor(ref)) .fail("Premise indices must be integers")
    if (step$rule == "forall_elim") .require_term(step$term)
  }
  .joint_signature(c(assumptions, axioms, if (!is.null(conclusion)) list(conclusion),
    lapply(steps, function(x) x$formula), lapply(Filter(function(x) x$rule == "forall_elim", steps), function(x) x$term)))
  matches <- function(x, xs) any(vapply(xs, function(y) alpha_equal(x, y), logical(1)))
  for (i in seq_along(steps)) {
    step <- steps[[i]]; refs <- step$premises; f <- step$formula
    required <- switch(step$rule, assumption = 0L, axiom = 0L, mp = 2L, and_intro = 2L, 1L)
    valid <- length(refs) == required && all(vapply(refs, function(j) j >= 1L && j < i, logical(1)))
    if (valid) {
      fs <- lapply(refs, function(j) steps[[j]]$formula)
      valid <- switch(step$rule,
        assumption = matches(f, assumptions),
        axiom = matches(f, axioms),
        mp = fs[[2L]]$kind == "implies" && alpha_equal(fs[[1L]], fs[[2L]]$args[[1L]]) && alpha_equal(f, fs[[2L]]$args[[2L]]),
        and_intro = f$kind == "and" && alpha_equal(f$args[[1L]], fs[[1L]]) && alpha_equal(f$args[[2L]], fs[[2L]]),
        and_left = fs[[1L]]$kind == "and" && alpha_equal(f, fs[[1L]]$args[[1L]]),
        and_right = fs[[1L]]$kind == "and" && alpha_equal(f, fs[[1L]]$args[[2L]]),
        forall_elim = fs[[1L]]$kind == "forall" && alpha_equal(f, substitute_formula(fs[[1L]]$args[[1L]], fs[[1L]]$name, step$term)),
        forall_intro = f$kind == "forall" && alpha_equal(f$args[[1L]], fs[[1L]]) &&
          !f$name %in% unlist(lapply(assumptions, free_variables), use.names = FALSE))
    }
    if (!valid) return(.proof_result("REFUTED", assumptions, axioms, invalid_step = i, reason = "RULE_MISMATCH"))
  }
  if (!is.null(conclusion) && !alpha_equal(steps[[length(steps)]]$formula, conclusion))
    return(.proof_result("REFUTED", assumptions, axioms, invalid_step = length(steps), reason = "CONCLUSION_MISMATCH"))
  .proof_result("ESTABLISHED", assumptions, axioms, witness = steps)
}

#' Search a Bounded Finite Closure of Assumptions
#'
#' Search uses only modus ponens and conjunction projections. It inserts distinct
#' assumptions in order, scans facts left to right, tries left projection before
#' right projection and scans ordered modus-ponens pairs. Alpha-equivalent facts
#' are deduplicated. The budget counts all admitted steps, including assumptions.
#' A found proof is checked independently before success. Failure is UNKNOWN,
#' with BOUND_EXHAUSTED or SEARCH_SPACE_EXHAUSTED, never unprovability.
#' @param goal A formula to seek.
#' @param assumptions An unnamed list of trusted formulas.
#' @param max_steps An integer budget from 1 through 256.
#' @return A \code{goedel_result}. Success has status ESTABLISHED and a checked
#' proof witness. Details report termination_reason and steps_used.
#' @examples
#' a <- predicate("A"); b <- predicate("B")
#' bounded_proof_search(b, list(a, implication(a, b)))$status
#' bounded_proof_search(b, list(a))$details
#' @export
bounded_proof_search <- function(goal, assumptions = list(), max_steps = 64L) {
  .require_formula(goal); .formula_list(assumptions, "assumptions")
  .joint_signature(c(list(goal), assumptions))
  if (!is.numeric(max_steps) || is.logical(max_steps) || length(max_steps) != 1L ||
      is.na(max_steps) || !is.finite(max_steps) || max_steps != floor(max_steps) || max_steps < 1L || max_steps > 256L) .fail("max_steps must be an integer in 1..256")
  steps <- list(); keys <- character(); found <- FALSE; exhausted <- FALSE
  result <- function(reason) {
    success <- reason == "GOAL_FOUND"
    if (success && check_proof(steps, assumptions, conclusion = goal)$status != "ESTABLISHED") .fail("Internal search witness failed validation")
    .result(if (success) "ESTABLISHED" else "UNKNOWN", "BOUNDED_SEARCH", "bounded_derivability",
      assumptions, limitations = "Finite closure under modus ponens and conjunction projection; failure is not unprovability.",
      witness = if (success) steps else NULL, details = list(termination_reason = reason, steps_used = length(steps)))
  }
  add <- function(formula, rule, premises = list()) {
    key <- .wire_json(normalize(formula))
    if (key %in% keys) return(FALSE)
    if (length(steps) >= max_steps) { exhausted <<- TRUE; return(FALSE) }
    steps[[length(steps) + 1L]] <<- list(rule = rule, formula = formula, premises = premises)
    keys <<- c(keys, key)
    if (alpha_equal(formula, goal)) found <<- TRUE
    TRUE
  }
  for (f in assumptions) {
    add(f, "assumption")
    if (found) return(result("GOAL_FOUND"))
    if (exhausted) return(result("BOUND_EXHAUSTED"))
  }
  repeat {
    before <- length(steps); n <- length(steps)
    if (!n) break
    for (i in seq_len(n)) {
      f <- steps[[i]]$formula
      if (f$kind == "and") for (side in 1:2) {
        add(f$args[[side]], if (side == 1L) "and_left" else "and_right", list(i))
        if (found) return(result("GOAL_FOUND"))
        if (exhausted) return(result("BOUND_EXHAUSTED"))
      }
    }
    n <- length(steps)
    for (i in seq_len(n)) {
      f <- steps[[i]]$formula
      for (j in seq_len(n)) {
        g <- steps[[j]]$formula
        if (g$kind == "implies" && alpha_equal(f, g$args[[1L]])) {
          add(g$args[[2L]], "mp", list(i, j))
          if (found) return(result("GOAL_FOUND"))
          if (exhausted) return(result("BOUND_EXHAUSTED"))
        }
      }
    }
    if (length(steps) == before) break
  }
  result("SEARCH_SPACE_EXHAUSTED")
}

#' @export
print.goedel_result <- function(x, ...) {
  cat("<goedel_result ", x$mode, "> ", x$status, ": ", x$claim, "\n", sep = "")
  invisible(x)
}
