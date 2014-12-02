AI-backward-chaining
====================

Problem Description

You are given a knowledge base and a query sentence, and you need to determine if the query
can be inferred from the information given in the knowledge base. You are required to use
backward-chaining to solve this problem.

Input:
You will be given the knowledge base and the query in a text file called input.txt.
The first line of the input file contains the query. The second line contains an integer n specifying
the number of clauses in the knowledge base. The remaining lines contain the clauses in the
knowledge base, one per line. Each clause is written in one of the following forms:
1) as an implication of the form p1 ∧ p2 ∧ ... ∧ pn ⇒ q, whose premise is a conjunction of
atomic sentences and whose conclusion is a single atomic sentence.
2) as a fact with a single atomic sentence: q
Each atomic sentence is a predicate applied to a certain number of arguments. Note that
negation is not used in this homework.

Output:
If the query sentence can be inferred from the knowledge base, your output should be TRUE,
otherwise, FALSE. Your answer (TRUE/FALSE) should be made available in the file output.txt.
Sample:
The input file will be formatted as below:
Diagnosis(John,Infected)
6
HasSymptom(x,Diarrhea)=>LostWeight(x)
LostWeight(x)&Diagnosis(x,LikelyInfected)=>Diagnosis(x,Infected)
HasTraveled(x,Tiberia)&HasFever(x)=>Diagnosis(x,LikelyInfected)
HasTraveled(John,Tiberia)
HasFever(John)
HasSymptom(John,Diarrhea)

Note:
1. & denotes the AND operator.
2. => denotes the implication operator.
3. No other operators besides & and => are used.
4. Variables are denoted by a single lower case letter (For this homework, you can assume
that only variable x will be used. No other variables are used.)
5. All predicates (such as HasFever) and constants (such as John) begin with uppercase
letters.
6. You can assume that all predicates have at least one and at most two arguments.
7. You can assume that there will be no more than 10 clauses in the knowledge base.

Since the query can be inferred from the given clauses in the sample input file, the output file
will mention TRUE.
