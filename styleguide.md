ALPS Agda Style Guide
=====================

Some rules for agda code that everyone has to follow when working on
shared code. Code you keep in your personal classrooms don't have to
live up to the standard but it's a good idea use them anyway!

Use only ascii characters.
---------------------

Agda allows and sometimes the tutorials promote use of non-ascii characters
because they look cool or are close to real math notation. This is bad
since we are all using different software when writing code and some characters
are more and less friendly with some software.

Use lots of arrows in type signatures.
--------------------------------------
You can skip alot of arrows in your type signatures in agda but we will try
to not use this syntactic sugar since it makes code less readable more often
than not. Example bad signature:

    foo : {x : Bar}(y : Baz) -> Qux

Good signature:

    foo : {x : Bar} -> (y : Baz) -> Qux

When you have multiple arguments of one type you can still put them in
one group. Example signature:

    foo : {x y : Bar} -> (z : Baz) -> Qux
    
Function and type names
-----------------------
Function names and constructors should start with lower case letters. In multi word names 
the words succeeding the first start with UPPER case letters.
    
    foo : ...
    fooBar : ...

Types should start with UPPER case letters

    data Type : set where


Structure / import-export rules
-------------------------------
Vandelay? Corvelay? TOO BE ADDED.
