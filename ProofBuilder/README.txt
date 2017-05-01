===============
PROOF BUILDER
===============

-- LTL
 * Contains a representation of the extended LTL logic.

-- LTLRules
 * Contains all legal rules as the datatype ⊨. The type
   defines program specific rules, pure LTL rules, and
   custom rules.
 * Program rules require a satisfaction relation between
   a program and a formula, as well as a program segment
   that matches the rule to be applied.
 * The LTL rules only require a satisfaction between a
   program and the precondition of the rule to be applied.
 * The custom rules require a pre- and postcondition.
   Considered to always be applicable if the precondition
   is met.
   
-- Label
 * Represents the labels of program segments.
 
 -- Program
 * Contains a representation of concurrent programs. A
   program is basically a pointer to an entry point. The
   rest of the program is built using the "postcondition"
   of each segment, namely a label of the next segment.
   
-- ProofBuilder
 * Module where some example proofs are built. Currently only
   supporting liveness proofs.
