#lang info
(define collection "rico-blaze")
(define deps '("base" "https://github.com/michaelballantyne/syntax-spec.git"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib"))
(define scribblings '(("scribblings/rico-blaze.scrbl" ())))
(define pkg-desc "A tiny CPU written in a custom HDL")
(define version "0.0")
(define pkg-authors '("Mike Delmonaco"))
(define license '(Apache-2.0 OR MIT))
