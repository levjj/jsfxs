macro __fxstr {
    case { _ $fx }
      => { letstx $tokenStr = [makeValue("__@fx:" + unwrapSyntax(#{$fx}), #{$fx})];
           return #{ $tokenStr } }
}
macro __varfxstr {
    case { _ $var $fx }
      => { letstx $tokenStr = [makeValue("__@var:" + unwrapSyntax(#{$var}) + ":!" + unwrapSyntax(#{$fx}), #{$fx})];
           return #{ $tokenStr } }
}

macro funce {
    rule { () $oargs ($eff ...) { $s ... } }
      => { function $oargs { $( __fxstr $eff ;) ... $s ... } }
    rule { (, $args ...) $oargs $eff $s }
      => { funce ($args ...) $oargs $eff $s }

    rule { ($arg:ident fx[$(! $e:ident) (,) ...] $args ...) () $eff { $s ... } }
      => { funce ($args ...) ($arg) $eff { $( __varfxstr $arg $e ;) ...  $s ... } }
    rule { ($arg:ident $args ...) () $eff $s }
      => { funce ($args ...) ($arg) $eff $s }

    rule { ($arg:ident fx[$(! $e:ident) (,) ...] $args ...) ($oargs ...) $eff { $s ... } }
      => { funce ($args ...) ($arg, $oargs ...) $eff { $( __varfxstr $arg $e ;) ...  $s ... } }
    rule { ($arg:ident $args ...) ($oargs ...) $eff $s }
      => { funce ($args ...) ($arg, $oargs ...) $eff $s }
}

let function = macro {
    rule { ($args ...) { $s ... } }
      => { funce ($args ...) () () { $s ... }}
    rule { ($args ...) fx [$e:ident (,) ...] { $s ... } }
      => { funce ($args ...) () ($e ...) { $s ... }}
}

export function;
