;; SPDX-License-Identifier: MPL-2.0
;; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
;;
;; manifest.scm — the Guix development shell for resource-algebra.
;;
;;   guix shell -m manifest.scm                  # or: just dev-shell
;;   guix time-machine -C channels.scm -- shell -m manifest.scm   # the pinned Guix
;;
;; Languages detected here: none. This repository has no FFI or build language (the
;; scaffold was removed 2026-11-16); the Agda proofs are checked by scripts/check-agda.sh.
;; Tools Guix does not package come from mise, which this shell provides:
;;   guix shell -m manifest.scm -- mise install
;; Canon: hyperpolymath/standards 3-practice/provisioning/PROVISIONING-STANDARD.adoc
(specifications->manifest
 (list "git" "bash" "coreutils" "nss-certs" "just" "mise"
       "shellcheck"))
