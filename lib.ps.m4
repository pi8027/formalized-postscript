% primitive instructions

/pair { [ 3 2 roll /exec cvx 4 3 roll /exec cvx ] cvx exec } def
/cons { [ 3 1 roll /pair cvx ] cvx } def
/quote { [ exch ] cvx } def

% boolean values ADD_MODULES(FormalPS.Bool)

/boolfalse  {EMBED(instbool false)} def
/booltrue   {EMBED(instbool true)} def
/boolnot    {EMBED(instnot)} def
/boolif     {EMBED(instif)} def
/boolexecif {EMBED(instexecif)} def
/boolxor    {EMBED(instxor)} def
/booland    {EMBED(instand)} def
/boolor     {EMBED(instor)} def

/boolenc {
    { booltrue }{ boolfalse } ifelse
} def

/booldec {
    { true }{ false } boolexecif
} def

% natural numbers ADD_MODULES(FormalPS.Nat)

/natsucc   {EMBED(inst_succn)} def
/natadd    {EMBED(inst_addn)} def
/natmult   {EMBED(inst_muln)} def
/nateven   {EMBED(inst_even)} def
/natiszero {EMBED(inst_iszero)} def
/natpred   {EMBED(inst_predn)} def
/natsub    {EMBED(inst_subn)} def
/natle     {EMBED(inst_leqn)} def
/natdivmod {EMBED(inst_divmodn)} def
/natgcd    {EMBED(inst_gcdn)} def

/natenc {
    {EMBED(instnat 0)} exch { natsucc } repeat
} def

/natdec {
    0 exch { 1 add } exch exec exec
} def
