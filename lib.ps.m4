% primitive instructions

/pair { [ 3 2 roll /exec cvx 4 3 roll /exec cvx ] cvx exec } def
/cons { [ 3 1 roll /pair cvx ] cvx } def
/quote { [ exch ] cvx } def

% boolean values ADD_MODULES(PsBool)

/boolfalse  EMBEDPUSH(instfalse) def
/booltrue   EMBEDPUSH(insttrue) def
/boolnot    EMBEDPUSH(instnot) def
/boolif     EMBEDPUSH(instif) def
/boolexecif EMBEDPUSH(instexecif) def
/boolxor    EMBEDPUSH(instxor) def
/booland    EMBEDPUSH(instand) def
/boolor     EMBEDPUSH(instor) def

/boolenc {
    { booltrue }{ boolfalse } ifelse
} def

/booldec {
    { true }{ false } boolexecif
} def

% natural numbers ADD_MODULES(PsNat)

/natsucc   EMBEDPUSH(instnat_succ) def
/natadd    EMBEDPUSH(instnat_add) def
/natmult   EMBEDPUSH(instnat_mult) def
/nateven   EMBEDPUSH(instnat_even) def
/natiszero EMBEDPUSH(instnat_iszero) def
/natpred   EMBEDPUSH(instnat_pred) def
/natsub    EMBEDPUSH(instnat_sub) def
/natle     EMBEDPUSH(instnat_le) def

/natenc {
    EMBEDPUSH(instnat 0) exch { natsucc } repeat
} def

/natdec {
    0 exch { 1 add } exch exec exec
} def
