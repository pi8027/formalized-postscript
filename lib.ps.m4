% primitive instructions
/pair { [ 3 2 roll /exec cvx 4 3 roll /exec cvx ] cvx exec } def
/cons { [ 3 1 roll /pair cvx ] cvx } def
/quote { [ exch ] cvx } def

% boolean values
ADD_MODULES(PsBool)dnl
/boolenc {
    {
        EMBEDPUSH(proj1_sig exists_true)
    } {
        EMBEDPUSH(proj1_sig exists_false)
    } ifelse
} def

/booldec {
    {
        true
    } {
        false
    } EMBED(proj1_sig exists_execif)
} def

% natural numbers
ADD_MODULES(PsNat)dnl
/natenc {
    EMBEDPUSH(proj1_sig (exists_instnat 0)) exch {
        EMBED(proj1_sig exists_instnat_succ)
    } repeat
} def

/natdec {
    0 exch { 1 add } exch exec exec
} def
