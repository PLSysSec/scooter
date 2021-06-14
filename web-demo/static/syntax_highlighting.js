define('ace/mode/custom', [], function(require, exports, module) {

  var oop = require("ace/lib/oop");
  var TextMode = require("ace/mode/text").Mode;
  var Tokenizer = require("ace/tokenizer").Tokenizer;
  var ExampleHighlightRules = require("ace/mode/policy_highlight_rules").ExampleHighlightRules;

  var Mode = function() {
    this.HighlightRules = ExampleHighlightRules;
  };
  oop.inherits(Mode, TextMode);

  (function() {
    this.lineCommentStart = "--";
    this.blockComment = {
      start: "->",
      end: "<-"
    };
  }).call(Mode.prototype);

  exports.Mode = Mode;
});

define('ace/mode/policy_highlight_rules', [], function(require, exports, module) {
  var oop = require("ace/lib/oop");
  var TextHighlightRules = require("ace/mode/text_highlight_rules").TextHighlightRules;

  var ExampleHighlightRules = function() {

    var keywordMapper = this.createKeywordMapper({
      "variable.language": "this",
      "keyword": "if|then|else|match",
      "constant.language": "public|none|true|false|null"
    }, "text", true);

    this.$rules = {
      "start": [
      {
	      token: "keyword",
	      regex: /create:|delete:|read:|write:/,
      },
      {
	      token: "operator",
	      regex: "::|->"
      },
      {	      token: "constant.numeric",
              regex: /\d+(?:[.](\d)*)?|[.]\d+/
      },
      {
	      token: "constant",
	      regex: /@(static-)?principal/
      },
      {
	      token: "function",
	      regex: /\.flat_map/
      },
      {
        token: "comment.line",
        regex: /^\s*#.*$/,
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
      }]
    };
    this.normalizeRules()
  };

  oop.inherits(ExampleHighlightRules, TextHighlightRules);

  exports.ExampleHighlightRules = ExampleHighlightRules;

});
