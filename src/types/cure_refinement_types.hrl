%% Cure Refinement Types - Record Definitions
%% Shared header for refinement type data structures

-ifndef(CURE_REFINEMENT_TYPES_HRL).
-define(CURE_REFINEMENT_TYPES_HRL, true).

%% Refinement Type Record
%% Represents a type with logical predicates verified by SMT
%% Example: {x : Int | x > 0}
-record(refinement_type, {
    base_type :: term(),      % The base type being refined (e.g., Int, Bool)
    variable :: atom(),       % The refinement variable (e.g., 'x')
    predicate :: term(),      % The refinement predicate (AST expr)
    location :: term()        % Source location for error reporting
}).

-endif. % CURE_REFINEMENT_TYPES_HRL
