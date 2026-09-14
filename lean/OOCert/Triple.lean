/-!
# Terms and triples

A term is kept in its N-Triples spelling: `<iri>`, `_:label`, or a literal
with its quotes, datatype or language tag. The checker never looks inside a
term. Two terms are the same term when their spellings are the same string,
which is exactly how the engine's interner treats them, and the certificate
is written by that interner.

Blank nodes are therefore constants with a scope of one certificate. That is
the skolemised reading of a graph, the one every OWL 2 RL materialiser uses;
the certificate and the asserted graph it refers to come from the same run,
so a label names the same node in both files.
-/
namespace OOCert

abbrev Term := String

structure Triple where
  s : Term
  p : Term
  o : Term
deriving DecidableEq, Hashable, Repr

/-! The vocabulary the rules mention, in N-Triples spelling. -/
namespace V
def type : Term := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"
def first : Term := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#first>"
def rest : Term := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#rest>"
def nil : Term := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#nil>"
def subClassOf : Term := "<http://www.w3.org/2000/01/rdf-schema#subClassOf>"
def subPropertyOf : Term := "<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>"
def domain : Term := "<http://www.w3.org/2000/01/rdf-schema#domain>"
def range : Term := "<http://www.w3.org/2000/01/rdf-schema#range>"
def transitiveProperty : Term := "<http://www.w3.org/2002/07/owl#TransitiveProperty>"
def symmetricProperty : Term := "<http://www.w3.org/2002/07/owl#SymmetricProperty>"
def inverseOf : Term := "<http://www.w3.org/2002/07/owl#inverseOf>"
def sameAs : Term := "<http://www.w3.org/2002/07/owl#sameAs>"
def equivalentClass : Term := "<http://www.w3.org/2002/07/owl#equivalentClass>"
def equivalentProperty : Term := "<http://www.w3.org/2002/07/owl#equivalentProperty>"
def onProperty : Term := "<http://www.w3.org/2002/07/owl#onProperty>"
def someValuesFrom : Term := "<http://www.w3.org/2002/07/owl#someValuesFrom>"
def allValuesFrom : Term := "<http://www.w3.org/2002/07/owl#allValuesFrom>"
def hasValue : Term := "<http://www.w3.org/2002/07/owl#hasValue>"
def intersectionOf : Term := "<http://www.w3.org/2002/07/owl#intersectionOf>"
def unionOf : Term := "<http://www.w3.org/2002/07/owl#unionOf>"
end V

end OOCert
