rule #take(N, #padToWidth(N, X) ++ Z ) => X
rule #asWord( #asByteStack( X ) ) => X

rule #hashedLocation("DappHub", BASE, OFFSET OFFSETS) => #hashedLocation("DappHub", keccakIntList(BASE OFFSET),       OFFSETS)

// propositional rules
rule notBool (P orBool Q) => (notBool P) andBool (notBool Q)
// this rule is not needed:
// rule notBool (P andBool Q) => (notBool P) orBool (notBool Q)
rule notBool (notBool P) => P

// new syntax for case-splitting lemmas
// may use existing #if in the future, avoiding it now for clarity

syntax K ::= "#mif" Bool "#mthen" K "#melse" K "#mfi" [function, poly(0, 2, 3)]
// --------------------------------------------------------------------------
rule P:Bool andBool ( #mif Q:Bool #mthen X:Bool #melse _ #mfi )
  => P andBool X
  requires (P impliesBool Q)
	  
rule P:Bool andBool ( #mif Q:Bool #mthen _ #melse Y:Bool #mfi )
  => P andBool Y
  requires (P impliesBool (notBool Q))

rule ( #mif Q:Bool #mthen X #melse _ #mfi )
  => X
  requires Q

rule ( #mif Q:Bool #mthen _ #melse Y #mfi )
  => Y
  requires (notBool Q)

// // general naturality (not possible)
// rule f (#mif P #mthen X #melse Y #mfi)
//   => (#mif P #mthen f ( X ) #melse f ( Y ) #mfi)

// // special case of naturality
rule notBool (#mif P #mthen X:Bool #melse Y:Bool #mfi)
  => (#mif P #mthen (notBool X) #melse (notBool Y) #mfi)

// lemmas to tell us that our non-overflow conditions are sufficient
rule (#unsigned(A) -Word #unsigned(B)) => #unsigned(A -Int B)
  requires #rangeSInt(256, A)
  andBool #rangeSInt(256, B)
  andBool #rangeSInt(256, A -Int B)

// n.b. how + cases use +Int because of earlier application of +Word 
rule (#unsigned(A) +Int #unsigned(B)) => #unsigned(A +Int B)
  requires #rangeSInt(256, A)
  andBool #rangeSInt(256, B)
  andBool #rangeSInt(256, A +Int B)

rule #signed(#unsigned(W)) => W
  requires #rangeSInt(256, W)

rule #unsigned(#signed(W)) => W
  requires #rangeUInt(256, W)

rule W0 s<Word W1 => #signed(W0) <Word #signed(W1)

// lemmas to tell us that our non-overflow conditions are necessary for
// the overflow checks in iadd and isub

rule #signed (#unsigned(A) -Word #unsigned(B)) <Int A
  => (#mif (0 <Int B)
      #mthen (A -Int B >=Int minSInt256)
      #melse notBool (A -Int B <=Int maxSInt256)
      #mfi)
  requires #rangeSInt(256, A)
  andBool #rangeSInt(256, B)

rule A <Int #signed (#unsigned(A) -Word #unsigned(B))
  => (#mif (0 >Int B)
      #mthen (A -Int B <=Int maxSInt256)
      #melse notBool (A -Int B >=Int minSInt256)
      #mfi)
  requires #rangeSInt(256, A)
  andBool #rangeSInt(256, B)

// n.b. how + cases use chop and +Int because of earlier application of +Word 
rule #signed (chop (#unsigned(A) +Int #unsigned(B))) <Int A
  => (#mif (B <Int 0)
      #mthen (A +Int B >=Int minSInt256)
      #melse notBool (A +Int B <=Int maxSInt256)
      #mfi)
  requires #rangeSInt(256, A)
  andBool #rangeSInt(256, B)

rule A <Int #signed (chop (#unsigned(A) +Int #unsigned(B)))
  => (#mif (0 <Int B)
      #mthen (A +Int B <=Int maxSInt256)
      #melse notBool (A -Int B >=Int minSInt256)
      #mfi)
  requires #rangeSInt(256, A)
  andBool #rangeSInt(256, B)
 

