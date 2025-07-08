------------------------------ MODULE Utils ------------------------------
\* There are a few utilities here copied over from https://github.com/tlaplus/CommunityModules (MIT license)

LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE TLC
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets

CONSTANT Nothing

\* From https://github.com/tlaplus/CommunityModules (MIT license)
PrintVal(id, exp) == Print(<<id, exp>>, TRUE)
IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b
SeqToSet(s) == {s[i] : i \in DOMAIN s}
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
SetToSeqs(S) == LET D == 1..Cardinality(S) IN { f \in [D -> S] : \A i,j \in D : i # j => f[i] # f[j] }
Range(f) == { f[x] : x \in DOMAIN f }

Min(S) == CHOOSE s \in S : \A t \in S : s <= t
Max(S) == CHOOSE s \in S : \A t \in S : s >= t

\* The first element in a sequence where test(e) is TRUE; Nothing if the test is FALSE for all elements.
FirstMatch(haystack, test(_)) ==
    LET i == CHOOSE i \in 1..(Len(haystack)+1): (i > Len(haystack)) \/ test(haystack[i])
    IN IF i > Len(haystack) THEN Nothing ELSE haystack[i]
LOCAL Check_FirstMatch == FirstMatch(<<1,2,3>>, LAMBDA x: x = 2) = 2
                       /\ FirstMatch(<<1,2,3>>, LAMBDA x: x = 4) = Nothing
                       /\ FirstMatch(<<>>, LAMBDA x: x = 0) = Nothing

\* The set element where test(e) is TRUE; Nothing if the test is false for all elements.
Get(haystack, test(_)) == LET matches == { x \in haystack : test(x) }
                          IN IF matches = {} THEN Nothing ELSE CHOOSE x \in matches : TRUE
LOCAL Check_Get == Get({1,2,3}, LAMBDA x: x = 2) = 2
                /\ Get({1,2,3}, LAMBDA x: x = 4) = Nothing
                /\ Get({}, LAMBDA x: x = 0) = Nothing

\* A sequence that contains zero needles.
SeqWithout(haystack, needle) == SelectSeq(haystack, LAMBDA x: x # needle)
LOCAL Check_SeqWithout == SeqWithout(<<>>, 1) = <<>>
                       /\ SeqWithout(<<1, 2, 3>>, 2) = <<1, 3>>
                       /\ SeqWithout(<<1, 2, 3>>, 4) = <<1, 2, 3>>

\* <<1, 2, 3>> ==> <<2, 3, 1>>
SeqRotLeft(seq) == IF Len(seq) > 0 THEN Tail(seq) \o <<Head(seq)>> ELSE seq

\* Converts {<<k1, v1>>, <<k2, v2>>, ...} into a function [k |-> v]. Keys must be unique.
FunFromTupleSet(S) == [
    k \in {p[1] : p \in S} |-> CHOOSE v \in {r[2] : r \in S} : <<k, v>> \in S
]
LOCAL Check_FunFromTupleSet == FunFromTupleSet({<<1, 11>>, <<2, 12>>, <<3, 13>>})[1] = 11
                            /\ FunFromTupleSet({<<1, 11>>, <<2, 12>>, <<3, 13>>})[2] = 12
                            /\ FunFromTupleSet({<<1, 11>>, <<2, 12>>, <<3, 13>>})[3] = 13

Check_Utils == Check_FirstMatch
            /\ Check_Get
            /\ Check_SeqWithout
            /\ Check_FunFromTupleSet
========================================================================================================================
