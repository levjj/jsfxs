(set-logic UF)
(set-option :produce-models true)

(declare-datatypes () ((Func <% for(var i = 1; i <= funcs; i++) { %> (F<%=i%>) <% } %>)))
(declare-datatypes () ((Obj <% for(var i = 1; i <= objs; i++) { %> (O<%=i%>) <% } %>)))
(declare-datatypes () ((Var <% for(var i = 1; i <= vars; i++) { %> (V<%=i%>) <% } %>)))
(declare-datatypes () ((Str (S0) <% for(var i = 1; i <= strs; i++) { %> (S<%=i%>) <% } %>)))
(declare-datatypes () ((Arg <% for(var i = 1; i <= args; i++) { %> (A<%=i%>) <% } %>)))

(declare-datatypes () ((Node
                         (Var (varname Var))
                         (Res (resf Func))
                         (This (thisf Func))
                         (Arg (argf Func) (argi Arg))
                         (Prop (propobj Obj) (propname Str)))))

; n = { ... }
(declare-fun hasobj (Node Obj) Bool)

; n = function f() { ... }
(declare-fun hasfunc (Node Func) Bool)

; prototypes
(declare-fun proto (Func) Obj)

; to = from
(define-fun flow ((from Node) (to Node)) Bool
  (and
    (forall ((func Func)) (=> (hasfunc from func) (hasfunc to func)))
    (forall ((obj Obj)) (=> (hasobj from obj) (hasobj to obj)))))

; to = fun()
(define-fun flow-res ((fun Node) (to Node)) Bool
  (forall ((f Func))
    (=> (hasfunc fun f)
        (flow (Res f) to))))

; to = new fun()
(define-fun flow-res-cons ((fun Node) (to Node)) Bool
  (forall ((f Func))
    (=> (hasfunc fun f)
        (hasobj to (proto f)))))

; _ = fun( ... a_i ... )
(define-fun flow-arg ((from Node) (fun Node) (arg Arg)) Bool
  (forall ((f Func))
    (=> (hasfunc fun f)
        (flow from (Arg f arg)))))

; to = obj.p
(define-fun flow-get ((obj Node) (prop Str) (to Node)) Bool
  (forall ((o Obj))
    (=> (hasobj obj o)
        (flow (Prop o prop) to))))

; obj.p = from
(define-fun flow-set ((from Node) (obj Node) (prop Str)) Bool
  (forall ((o Obj))
    (=> (hasobj obj o)
        (ite (= prop S0)
             (forall ((p Str)) (flow from (Prop o p)))
             (flow from (Prop o prop))))))

; _ = obj.prop()
(define-fun flow-this ((obj Node) (prop Str)) Bool
  (forall ((o Obj) (f Func))
    (=> (hasobj obj o)
        (ite (= prop S0)
             (forall ((p Str))
               (=> (hasfunc (Prop o p) f)
                   (hasobj (This f) o)))
             (=> (hasfunc (Prop o prop) f)
                 (hasobj (This f) o))))))

; _ = obj[*]
(assert
  (forall ((obj Obj) (p Str))
    (flow (Prop obj p) (Prop obj S0))))


<% _.each(constraints, function(c) { %>
(assert <%=c%>)
<% }) %>

(check-sat)
(get-model)
