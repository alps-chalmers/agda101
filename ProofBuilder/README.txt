===============
PROOF BUILDER
===============


-- CPL
* Contains the representation of the CPL. A program is basically
  a pointer to an entry point. The entry point refers to the main
 statement of the program.

-- ELTL
 * Contains a representation of the extended LTL logic.

-- SatRel
 * Contains all legal rules as the datatype ⊨. The type
   defines program specific rules and pure LTL rules.
 * Program rules require a satisfaction relation between
   a program and a formula, as well as a program statement
   that matches the rule to be applied.
 * The LTL rules only require a satisfaction between a
   program and the precondition of the rule to be applied.

-- Safety verifier
  * Coming soon.
