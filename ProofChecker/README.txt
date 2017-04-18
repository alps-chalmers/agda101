
Program.agda
* Representation of simple concurrent programs in agda.
* Contains data types for:
  - Variables for natural numbers and booleans.
  - Expressions for natural numbers and booleans.
  - Statements representing single program statements,
    for example assignments.
  - Code segments. Can be regular single-line segments,
    a block containing a list of segments, a parallel
    segment containing lists of segments that are run
    in parallel, and while loops containing a boolean expression
    and a segment.
  - Program that simply takes a segment (preferably a block).
  
LTL.agda
* Regular LTL extended with Owiki Lamport.

Translator.agda
* Translates a program representation into Hoare-style triples.
* Contains data types for:
  - Actions, reference to the type of program statement/execution.
  - TransRel, transition relations of the programs. Is represented
    as Hoare-style triples containing pre- and postconditions (LTL),
    as well as the corresponding action.
 * The main function "translate" translates a given program into a
   list TransRels. The translator consists of two parts, first handling
   the translation of single segments, and the second creating the transition
   relation between all segments of the program.

Rules-agda
* Represents all available rules to be used in the proofs.
* A rule can be one of three different types:
  - Program rules, used for program specific actions.
  - Regular LTL rules.
  - Custom rules, basically axioms supplied by the user.
* Contains a main function "applyRule" which takes a translation of
  a program, an LTL which is currently true, and a rule to be used.
  The function is used as a step in a proof. The function checks if
  the rule can be applied legally.

ProofChecker.agda
* The main module of the directory, contatining data types for proof steps
  and proofs. 
* Its main function "proofCheck" takes a program, custom rules, a proof, a goal for
  the proof, and the initial truth (LTL). Returns whether or not the proof is
  valid. If not, then an appropriate error message is shown.
