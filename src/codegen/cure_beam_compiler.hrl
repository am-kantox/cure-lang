%% BEAM Compiler Records for Cure Language
%% Defines structures for BEAM compilation pipeline

-record(beam_instr, {
    op :: atom(),               % Operation name (load_param_int, call, etc.)
    args = [] :: list(),        % Operation arguments
    location :: any()           % Source location for debugging
}).