/*
 * Cure Language Definition for highlight.js
 * Language: Cure
 * Description: Dependent types, FSMs, and verification for the BEAM
 * Author: Cure Programming Language
 * Website: https://github.com/ammotion/cure
 */

(function(hljs) {
  return {
    name: 'Cure',
    aliases: ['cure'],
    case_insensitive: false,
    keywords: {
      keyword:
        'def end do match when let in as where ' +
        'module import export process fsm state states initial event timeout ' +
        'receive send spawn transition guard action invariant eventually always until property ' +
        'record type fn typeclass trait instance impl derive class curify for',
      built_in:
        'Ok Error Some None Unit ok error Nat Atom Zero Succ Pred Self',
      literal:
        'true false'
    },
    contains: [
      // Comments
      hljs.COMMENT('#', '$', {
        contains: [
          {
            className: 'doctag',
            begin: '\\b(TODO|FIXME|NOTE|XXX)\\b'
          }
        ]
      }),
      
      // Strings with interpolation
      {
        className: 'string',
        variants: [
          {
            begin: '"',
            end: '"',
            contains: [
              hljs.BACKSLASH_ESCAPE,
              {
                className: 'subst',
                begin: '#{',
                end: '}',
                contains: [] // Will be populated with TOP
              }
            ]
          }
        ]
      },
      
      // Quoted atoms
      {
        className: 'symbol',
        begin: "'",
        end: "'",
        contains: [hljs.BACKSLASH_ESCAPE]
      },
      
      // Atoms (starting with :)
      {
        className: 'symbol',
        begin: ':[a-zA-Z_][a-zA-Z0-9_?]*'
      },
      
      // Numbers
      {
        className: 'number',
        variants: [
          { begin: '\\b\\d+\\.\\d+\\b' }, // Float
          { begin: '\\b\\d+\\b' }         // Integer
        ],
        relevance: 0
      },
      
      // Function definitions
      {
        className: 'title function',
        begin: '\\b(def|def_erl|curify)\\s+',
        end: '[\\(\\:]',
        excludeEnd: true,
        keywords: 'def def_erl curify',
        contains: [
          {
            className: 'title',
            begin: '[a-z_][a-zA-Z0-9_?]*',
            relevance: 0
          }
        ]
      },
      
      // Module/FSM/Record names
      {
        className: 'title class',
        begin: '\\b(module|import|fsm|record|typeclass|trait|class|instance|impl)\\s+',
        end: '\\s',
        excludeEnd: true,
        keywords: 'module import fsm record typeclass trait class instance impl',
        contains: [
          {
            className: 'title',
            begin: '[A-Z][a-zA-Z0-9_]*',
            relevance: 0
          }
        ]
      },
      
      // Type names (capitalized identifiers)
      {
        className: 'type',
        begin: '\\b[A-Z][a-zA-Z0-9_]*\\b',
        relevance: 0
      },
      
      // Operators
      {
        className: 'operator',
        begin: '(=>|->|-->|::|\\|>|\\+\\+|--|\\+|-|\\*|/|%|<=|>=|<>|==|!=|<|>|\\||<\\$|\\$>|<\\*>|\\*>|<\\*|>>=|>>|\\band\\b|\\bor\\b|\\bnot\\b)',
        relevance: 0
      },
      
      // Delimiters
      {
        className: 'punctuation',
        begin: '[\\(\\)\\[\\]\\{\\},;:\\.]',
        relevance: 0
      }
    ]
  };
})(hljs || {});

// Register the language
if (typeof hljs !== 'undefined') {
  hljs.registerLanguage('cure', function(hljs) {
    return (function(hljs) {
      return {
        name: 'Cure',
        aliases: ['cure'],
        case_insensitive: false,
        keywords: {
          keyword:
            'def end do match when let in as where ' +
            'module import export process fsm state states initial event timeout ' +
            'receive send spawn transition guard action invariant eventually always until property ' +
            'record type fn typeclass trait instance impl derive class curify for',
          built_in:
            'Ok Error Some None Unit ok error Nat Atom Zero Succ Pred Self',
          literal:
            'true false'
        },
        contains: [
          // Comments
          hljs.COMMENT('#', '$', {
            contains: [
              {
                className: 'doctag',
                begin: '\\b(TODO|FIXME|NOTE|XXX)\\b'
              }
            ]
          }),
          
          // Strings with interpolation
          {
            className: 'string',
            variants: [
              {
                begin: '"',
                end: '"',
                contains: [
                  hljs.BACKSLASH_ESCAPE,
                  {
                    className: 'subst',
                    begin: '#{',
                    end: '}',
                    contains: [] // Will be populated with TOP
                  }
                ]
              }
            ]
          },
          
          // Quoted atoms
          {
            className: 'symbol',
            begin: "'",
            end: "'",
            contains: [hljs.BACKSLASH_ESCAPE]
          },
          
          // Atoms (starting with :)
          {
            className: 'symbol',
            begin: ':[a-zA-Z_][a-zA-Z0-9_?]*'
          },
          
          // Numbers
          {
            className: 'number',
            variants: [
              { begin: '\\b\\d+\\.\\d+\\b' }, // Float
              { begin: '\\b\\d+\\b' }         // Integer
            ],
            relevance: 0
          },
          
          // Function definitions
          {
            className: 'title function',
            begin: '\\b(def|def_erl|curify)\\s+',
            end: '[\\(\\:]',
            excludeEnd: true,
            keywords: 'def def_erl curify',
            contains: [
              {
                className: 'title',
                begin: '[a-z_][a-zA-Z0-9_?]*',
                relevance: 0
              }
            ]
          },
          
          // Module/FSM/Record names
          {
            className: 'title class',
            begin: '\\b(module|import|fsm|record|typeclass|trait|class|instance|impl)\\s+',
            end: '\\s',
            excludeEnd: true,
            keywords: 'module import fsm record typeclass trait class instance impl',
            contains: [
              {
                className: 'title',
                begin: '[A-Z][a-zA-Z0-9_]*',
                relevance: 0
              }
            ]
          },
          
          // Type names (capitalized identifiers)
          {
            className: 'type',
            begin: '\\b[A-Z][a-zA-Z0-9_]*\\b',
            relevance: 0
          },
          
          // Operators
          {
            className: 'operator',
            begin: '(=>|->|-->|::|\\|>|\\+\\+|--|\\+|-|\\*|/|%|<=|>=|<>|==|!=|<|>|\\||<\\$|\\$>|<\\*>|\\*>|<\\*|>>=|>>|\\band\\b|\\bor\\b|\\bnot\\b)',
            relevance: 0
          },
          
          // Delimiters
          {
            className: 'punctuation',
            begin: '[\\(\\)\\[\\]\\{\\},;:\\.]',
            relevance: 0
          }
        ]
      };
    })(hljs);
  });
}
