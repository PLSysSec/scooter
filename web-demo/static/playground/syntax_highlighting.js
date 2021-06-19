define('ace/mode/custom', [], function (require, exports, module) {

  var oop = require("ace/lib/oop");
  var TextMode = require("ace/mode/text").Mode;
  var Tokenizer = require("ace/tokenizer").Tokenizer;
  var ExampleHighlightRules = require("ace/mode/policy_highlight_rules").ExampleHighlightRules;
  var Mode = function () {
    this.HighlightRules = ExampleHighlightRules;
  };
  oop.inherits(Mode, TextMode);

  (function () {
    this.lineCommentStart = "#";
  }).call(Mode.prototype);

  exports.Mode = Mode;
});

define('ace/mode/policy_highlight_rules', [], function (require, exports, module) {
  var oop = require("ace/lib/oop");
  var TextHighlightRules = require("ace/mode/text_highlight_rules").TextHighlightRules;

  var ExampleHighlightRules = function () {

    var keywordMapper = this.createKeywordMapper({
      "variable.language": "this",
      "keyword": "if|then|else|match",
      "constant.language": "public|none|true|false|null",
      "support.class": "Id|I64|Option|DateTime|F64|String|Set"
    }, "text", false);

    this.$rules = {
      "start": [
        {
          token: "keyword",
          regex: /create:|delete:|read:|write:/,
        },
        {
          token: "support.class",
          regex: /\w+(?=::)/
        },
        {
          token: "support.variable",
          regex: /\w+(?=\.)/
        },
        {
          token: "keyword.operator",
          regex: "::",
          next: "static-method"
        },
        {
          token: "constant.numeric",
          regex: /\d+(?:[.](\d)*)?|[.]\d+/
        },
        {
          token: "variable",
          regex: /\w+(?=\s*->)/
        },
        {
          token: "constant",
          regex: /@(static-)?principal/
        },
        {
          token: "support.function",
          regex: /\.(flat_)?map/
        },
        {
          token: "comment.line",
          regex: /#.*$/,
        }, {
          regex: "\\w+\\b",
          token: keywordMapper
        }, {
          token: "string",
          regex: '"',
          next: [{
            regex: /\\./,
            token: "escape.character"
          }, {
            regex: '"',
            token: "string",
            next: "start"
          }, {
            defaultToken: "string"
          }]
        }, {
          token: "numbers",
          regex: /\d+(?:[.](\d)*)?|[.]\d+/
        }],

      "static-method": [{
        token: "support.function",
        regex: /\w+/,
        next: "start"
      }]
    };
    this.normalizeRules()
  };

  oop.inherits(ExampleHighlightRules, TextHighlightRules);

  exports.ExampleHighlightRules = ExampleHighlightRules;

});



define('ace/mode/scooter-migration', [], function (require, exports, module) {

  var oop = require("ace/lib/oop");
  var TextMode = require("ace/mode/text").Mode;
  var Tokenizer = require("ace/tokenizer").Tokenizer;
  var ExampleHighlightRules = require("ace/mode/policy_highlight_rules").ExampleHighlightRules;

  var Mode = function () {
    this.HighlightRules = ExampleHighlightRules;
  };
  oop.inherits(Mode, TextMode);

  (function () {
    this.lineCommentStart = "--";
    this.blockComment = {
      start: "->",
      end: "<-"
    };
  }).call(Mode.prototype);

  exports.Mode = Mode;
});
