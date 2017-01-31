/*
This program creates two processes, which assign different values to the same global variable
The LTL formulae asssert some claims over the properties which are expected to hold during/after execution
*/

int n = 0, finish = 0;

active proctype P1(){
   n = 5; 
}

active proctype P2(){
    n = 6;
}

/*propositions*/
#define p (n == 5)
#define q (n == 6)

/*ltl formulae*/
//the end result will be a 5 or a 6
ltl result {always eventually (p || q)}

/*
Some simpler properties
ltl intermed1 {eventually p}
ltl intermed2 {eventually q}
*/
