(set-logic QF_AUFDTLIAFS)
(set-option :produce-models true)

(declare-datatypes () ((Func (f1))))
(declare-datatypes () ((Obj (o1))))
(declare-datatypes () ((Node (n1) (n2) (n3) (n4) (n5))))

(define-sort FuncSet () (Set Func))
(define-sort ObjSet () (Set Obj))
(declare-datatypes () ((Value (Val (funcs FuncSet) (objs ObjSet)))))

(declare-const sol (Array Node Value))

(define-fun hasobj ((n Node) (o Obj)) Bool
  (member o (objs (select sol n))))

(define-fun hasfunc ((n Node) (f Func)) Bool
  (member f (funcs (select sol n))))

(define-fun flow ((from Node) (to Node)) Bool
  (and (subset (funcs (select sol from)) (funcs (select sol to)))
       (subset (objs (select sol from)) (objs (select sol to)))))

(assert (hasobj n1 o1))
(assert (hasfunc n2 f1))
(assert (hasfunc n4 f1))

(assert (flow n1 n2))
(assert (flow n2 n3))

(check-sat)
(get-model)
