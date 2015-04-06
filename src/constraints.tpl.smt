(set-logic UFDT)
(set-option :produce-models true)

(declare-datatypes () ((Func <% for(var i = 1; i <= funcs; i++) { %> (F<%=i%>) <% } %>)))
(declare-datatypes () ((Obj <% for(var i = 1; i <= objs; i++) { %> (O<%=i%>) <% } %>)))
(declare-datatypes () ((Var <% for(var i = 1; i <= vars; i++) { %> (V<%=i%>) <% } %>)))
(declare-datatypes () ((Prop <% for(var i = 1; i <= props; i++) { %> (P<%=i%>) <% } %>)))
(declare-datatypes () ((Arg <% for(var i = 1; i <= args; i++) { %> (A<%=i%>) <% } %>)))

(declare-datatypes () ((Node
                         (Var (varname Var))
                         (Res (resf Func))
                         (Arg (argf Func) (argi Arg))
                         (Prop (propobj Obj) (propname Prop)))))

; n = { ... }
(declare-fun hasobj (Node Obj) Bool)

; n = function f() { ... }
(declare-fun hasfunc (Node Func) Bool)

; to = from
(define-fun flow ((from Node) (to Node)) Bool
  (forall ((func Func))
    (=> (hasfunc from func) (hasfunc to func))))

; to = fun()
(define-fun flow-res ((fun Node) (to Node)) Bool
  (forall ((f Func))
      (=> (hasfunc fun f)
          (flow (Res f) to))))

; _ = fun( ... a_i ... )
(define-fun flow-arg ((from Node) (fun Node) (arg Arg)) Bool
  (forall ((f Func))
      (=> (hasfunc fun f)
          (flow from (Arg f arg)))))

; to = obj.p
(define-fun flow-get ((obj Node) (prop Prop) (to Node)) Bool
  (forall ((o Obj))
      (=> (hasobj obj o)
          (flow (Prop o prop) to))))

; obj.p = from
(define-fun flow-set ((from Node) (obj Node) (prop Prop)) Bool
  (forall ((o Obj))
      (=> (hasobj obj o)
          (flow from (Prop o prop)))))

<% _.each(constraints, function(c) { %>
(assert <%=c%>)
<% }) %>

(check-sat)
(get-model)
