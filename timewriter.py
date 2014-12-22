#! /usr/bin/env python
# -*- coding: utf-8 -*-
#
# Code released in the Public Domain. You can do whatever you want with this package.
# Look at README file to see how to adapt this program.
# Originally written by Pierre Métras <pierre@alterna.tv> for the OLPC XO laptop.


"""Inference engine to write times in English (or other language).

Change the rules to adapt to another language. Caution: the rule parser does not
strictly check the syntax and many errors will remained ignored.

Usefull functions:
- print_rules(): Dump the set of rules.
- test_times(): Try to print all times from 00:00 to 23:59.
- write_time(hour, minute): Write the (hour, minute) in natural language.
- eval_rule(text): Translate the text according to the set of rules.

Example of usage:
-----------------
import timewriter

w = timewriter.TimeWriter("en")
s = w.write_time(2, 33)
print "It is %s."

prints --> It is thirty-three minutes past two in the morning.

How to tell time in English?
----------------------------
http://en.wikipedia.org/wiki/12-hour_clock
"""

#import pdb

import tokenize
import cStringIO
import re
import copy

from gettext import gettext as _

"""
Grammar for the rules:
----------------------
Root := Pattern
Pattern := Text? Pattern_call? Pattern?
Pattern_call := Pattern_name ( Argument [, Argument]* )
Text := string
Pattern_name := string
Argument := Dumb_variable_ | Variable | Value
Dumb_variable := '_'
Variable := string
Value := number
Rules := Rule ('|' Rules)*
Rule := Pattern_call Range_condition* '=>' Text? Pattern_call? Pattern?
Range_condition := '[' Argument '<' Argument ('<' Argument)? ']'

'#' can be used to concatenate two Texts or Pattern_call without a space between.
"""


class _Rule:
    """A rule is composed of conditions and a body.
        Rule: Conditions => Body

    Examples:
        number(8) => eight
        plural(1) =>
        plural(_) => s

    The inference engine tries to match a template with the conditions pattern of
    the rule, eventually binding the variables. If the rule matches, then the body
    of the rule is used, after substituting the variables by their values and
    eventually firing the other rules called in the body definition.
    """

    def __init__(self, pattern, ranges, body):
        """Create a new rule from its conditions, optional ranges and body.
        """
        self._pattern = pattern
        self._ranges = ranges
        self._body = body


    def get_pattern(self):
        """Gets the conditions pattern of the rule.
        Returns a list [rule_name, arg1, arg2...].
        """
        return self._pattern


    def get_ranges(self):
        """Gets the range condition to apply the rule.
        Returns a list [[arg1, arg2], [arg1, arg2, arg3]...].
        """
        return self._ranges


    def get_body(self):
        """Gets the body of the rule.
        Returns a list, for instance with two text fragments around another rule
        call, [text1, [rule_name, arg1, arg2], text2].
        """
        return self._body


    def __str__(self):
        """Gets the external representation of the rule as lists.
        """
        return "Rule: %s %s => %s" % (self._pattern, self._ranges, self._body)


    def __repr__(self):
        """
        Returns the external representation of the rule.
        """
        return self._repr_call(self._pattern) + self._repr_ranges(self._ranges) + " => " + self._repr_body(self._body)


    def _repr_call(self, call):
        """Returns the external representation of a rule call.
        """
        return "%s(%s)" % (call[0], ", ".join(str(x) for x in call[1:]))


    def _repr_ranges(self, ranges):
        """Returns the external repressentation of a rule ranges.
        """
        result = ""
        for r in ranges:
            if len(r) == 2:
                result += " [ %s < %s ]" % (r[0], r[1])
            else:
                result += " [ %s < %s < %s ]" % (r[0], r[1], r(2))
        return result


    def _repr_body(self, body):
        """Returns the external representation of a rule body.
        """
        result = ""
        for item in body:
            if isinstance(item, list):
                result += "#" + self._repr_call(item)
            else:
                result += item
        return result


class TimeWriter:
    """A class to print the time in natural language.
    """


    def __init__(self):
        """Create a time writer for the current language.
        The rules localized for a language are stored in the localized messages file.
        """
        self._rules = self.parse_rules(self._time_rules)


    # TRANS: The rules to print the time in the localized language.
    #
    # Example syntax:
    #     time(h, 15) => a quarter to hour(h) am_pm(h) |
    # The left hand side of the rule defines a pattern with a variable 'h' and a
    # value '15'.
    # The right hand side, when applied, will use the text "a quarter to " and call
    # the first rule matching hour(h) after substituting the variable 'h' by its value,
    # and call the rule matching am_pm(h).
    # Internal spaces are significant on the right side of a rule. In calls, all
    # arguments which are not numbers are considered to be variables. The rule parser
    # is very simple and will let many syntax errors go ignored.
    #
    # A rule ends with the character '|'.
    # The character '_' is a anonymous variable.
    # The character '#' can be used to concatenate two text fragments. For instance:
    #     plural(1) => |
    #     plural(_) => s |
    #     hour(h) => number(h) hour#plural(h) |
    # Use '\#' to use a # character, for instance in a pango color
    # tag like <span foreground="\#FF0055">
    #
    # You can put range conditions on firing a rule, with the syntax [var1 < var2] or
    # [var1 < var2 < var3]. For instance:
    #     hours(h) [h < 12] => in the morning |
    #     hours(h) [12 < h < 18] => in the afternoon |
    #     hours(_) => in the night |
    #
    # These rules will be called with the root pattern "time(hour, minute)", with the
    # variable 'hour' bound to the current hour and the variable 'minute' to the
    # current minute.
    # Order of rules is important. Rules are tried from first to last. So most precise
    # rule must be placed first in the list.
    #
    # You can validate your set of rules by running the command line:
    #     python timewriter.py LANG
    #
    # You should use pango markup to respect the same colors as for the clock hands.
    # Look at the README file from the activity for explanations on how to create
    # rules.
    _time_rules = _("""time(h, m) => What Time Is It?""")


    def _syntax_error(self, rule):
        """Print an error message when a rule can't be parsed.
        """
        raise SyntaxError("Syntax error in rule: %s" % rule)
    
    
    def print_rules(self):
        """Print the list of rules. Can be used to check the parser.
        """
        print "Rules = ["
        for i, rule in enumerate(self._rules):
            print "#%d %s" % (i, rule)
        print "]\nTotal = %d rules\n" % len(self._rules)
    
    
    def repr_rules(self):
        """Gets the external representation of the rules.
        """
        return " |\n".join(repr(rule) for rule in self._rules)
    
    
    def parse_rules(self, source):
        """Parse all the rules for the current language.
        Rules are a list of rule definitions separated by |.
            Rules := Rule ( '|' Rule )*
        Returns the list of rules.
        """
        self._rules = []
        for rule in source.split("|"):
            r = self._parse_rule(rule)
            self._rules.append(r)
        return self._rules
    
    
    def _parse_rule(self, source):
        """Parse a single rule.
        A rule is composed of a pattern and a body, separated by =>.
            Rule := Pattern_call Range_condition* '=>' Rule_body
        Return a rule definition object.
        """
        r = re.findall(r"\s*(\w+\s*\(.*?\))\s*(\[.*\])?\s*=>(.*)", source)
        if r[0] is None or r[0][0] == "" or r[0][2] == "":
            self._syntax_error(rule)
        pattern_call = self._parse_call(r[0][0])
        range_conditions = self._parse_ranges(r[0][1])
        rule_body = self._parse_body(r[0][2].strip())
        rule = _Rule(pattern_call, range_conditions, rule_body)
        return rule
    
    
    def _parse_call(self, source):
        """Parse a rule pattern or call.
        A rule call is similar to a function call.
            Rule_call := Rule_name '(' ( arg [',' arg]* ) ')'
        Returns a list [Rule_name, arg1, arg2...]
        """
        src = cStringIO.StringIO(source).readline
        src = tokenize.generate_tokens(src)
        token = src.next()
        if token[0] is not tokenize.NAME:
             self._syntax_error(source)
        call = [token[1]]
        token = src.next()
        if token[1] != "(":
             self._syntax_error(source)
        token = src.next()
        while token[1] != ")":
            try:
                call.append(int(token[1]))
            except ValueError:
                call.append(token[1])
            token = src.next()
            if token[1] == ",":
                token = src.next()
        return call


    def _parse_ranges(self, source):
        """Parse zero or many range conditions.
            Range_conditions := Range_condition*
            Range_condition := '[' arg1 '<' arg2 ('<' arg3)? ']'
        Returns a list [[arg11, arg12], [arg21, arg22, arg23]...]
        """
        if source == "":
            return None
        else:
            ranges = []
            for r in re.findall(r"\[\s*(.*?)\s*<\s*(.*?)\s*(?:<\s(.*?))?\s*\]", source):
                rang = []
                for x in r:
                    if x != "":
                        try:
                            rang.append(int(x))
                        except ValueError:
                            rang.append(x)
                ranges.append(rang)
            return ranges


    def _parse_body(self, source):
        """Parse the right hand side of a rule.
        We must preserve spaces in the rule body, so we use regular expression for parsing.
            Rule_body := text? Pattern_call? Rule_body?
        Returns a list [text, (pattern, arg1, arg2...), text, ...]
        '#' is a concatenation operator if not escaped by '\'
        """
        if not re.search(r"(\w+\s*\(.*?\))", source):
            # No rull call present
            return [source]
        else:
            body = []
            text = ""
            escaped = False
            for item in re.findall(r"(?:(\w+\s*\(.*?\))|(.))", source):
                if item[0] != "":
                    if text != "":
                        body.append(text)
                        text = ""
                    body.append(self._parse_call(item[0]))
                else:
                    if item[1] == "\\":
                        escaped= True
                    elif item[1] == "#":
                        if escaped:
                            text += item[1]
                            escaped = False
                    else:
                        text += item[1]
                        escaped = False
            if text != "":
                body.append(text)
            return body
    
    
    def write_time(self, hour, minute):
        """Gives the natural language translation of the time.
        For instance, write_time(3, 41) returns "three hours and forty-one minutes in the morning" with an English TimeWriter.
        """
        return self.eval_rule("time(%s, %s)" % (hour, minute))


    def eval_rule(self, source):
        """Evaluate the source against the set of rules.
        Example: eval_rule("It is time(15, 2).")
        """
        lst = self._parse_body(source)
        # lst = [text, [call, arg1, arg2..], text, ...]
        # The goal is now to flatten the list lst resolving all the calls
        lst = self._match_pattern(lst)
        return "".join(lst)
    
    
    def _match_pattern(self, patterns):
        """Match a list of patterns agains the set of rules.
        This engine stops at the first rule matching the pattern and eventually
        instanciates the variables, then recursively apply them in the body of the
        matched rule.
        Returns a list with all the patterns replaced by the rules bodies infered.
        If a pattern can't be matched, the engine produces no result in the resulting
        list. As we expect the set of rules to be complete (all submitted patterns
        fire at least one rule), we raise an exception if the number of items in the
        result is not the same as the number of patters submitted.
        """
        result = []
    
        for pattern in patterns:
            if isinstance(pattern, list):
                for rule in self._rules:
                    cond = rule.get_pattern()
    
                    # Simple tests first
                    if len(pattern) != len(cond):
                        continue
                    # Check that we test the same set of rules
                    if pattern[0] != cond[0]:
                        continue
    
                    # We use lazy rule body copy, only when there is a variable in the
                    # pattern. I've found that I got a 50% boost in performance doing
                    # that instead of doing the deepcopy from start.
                    body = None
    
                    # Now we check that the premises match and substitute all
                    # variables in rule body.
                    match = True
                    # The dictionary will keep the variable bindings
                    bind = {}
                    for i in range(1, len(pattern)):
                        # Dumb variable
                        if cond[i] == "_":
                            continue
    
                        # Variable instanciation
                        if not isinstance(cond[i], int):
                            if body is None:
                                body = copy.deepcopy(rule.get_body())
                            body = self._apply_var(cond[i], pattern[i], body)
                            bind[cond[i]] = pattern[i]
                            continue
    
                        if pattern[i] != cond[i]:
                            match = False
                            break

                    # Checking the range conditions to see if we can apply the rule
                    ranges = rule.get_ranges()
                    if match and ranges:
                        ranges = copy.deepcopy(ranges)
                        for r in ranges:
                            # Bind all variables
                            for i in range(0, len(r)):
                                if not isinstance(r[i], int):
                                    try:
                                        r[i] = bind[r[i]]
                                    except KeyError:
                                        #self._syntax_error(rule)
                                        match = False
                                        break

                            # Now check that the range is valid
                            if r[0] >= r[1]:
                                match = False
                                break
                            if len(r) > 2 and r[1] >= r[2]:
                                match = False
                                break

                    if match:
                        # Then we apply all the rule calls in the body of the rule
                        # that matched
                        if body is None:
                            body = copy.deepcopy(rule.get_body())
                        calls = True
                        while calls:
                            calls = False
                            for i in range(0, len(body)):
                                if isinstance(body[i], list):
                                    body[i] = "".join(self._match_pattern([body[i]]))
                                    calls = True
                        result.append("".join(body))
                        break
            else:
                result.append(pattern)
    
        if len(result) != len(patterns):
            raise Exception("There is a missing rule; match failed for pattern %s..." % patterns)
    
        return result


    def _apply_var(self, var, value, body):
        """Instanciate a variable in the body of a rule.
        Returns the body of the rule with that variable substituted by its value in all calls.    This function eventually changes the 'body' argument.
        """
        for elem in body:
            if isinstance(elem, list):
                for i in range(1, len(elem)):
                    if elem[i] == var:
                        elem[i] = value
        return body


    def test_times(self):
        """Check that the time rules are complete, printing all combinations.
        """
        print "***** Checking all times *****"

        for h in range(0, 24):
            for m in range(0, 60):
                str = self.write_time(h, m)
                print "time(%d, %d) -> %s" % (h, m, str)


    def set_rules(self, rules_source):
        """Assign the source of rules to the timewriter instance.
        The rules are parsed during the operation.
        """
        self._rules = self.parse_rules(rules_source)



def main():
    """Main entry point to test rules.
    """
    # import sys
    if len(sys.argv) == 1:
        print "Usage: python timewriter.py lang"
        print "Where lang is a ISO language code (en, fr, es...)"
        print "TimeWriter rules must be available in directory test-timewriter."
        exit(1)
    lang = sys.argv[1]
    test_mod = "test_timewriter." + lang + "_rules"
    import_mod = "from " + test_mod + " import _time_rules as test_rules"
    exec import_mod
    w = TimeWriter()
    w.set_rules(test_rules)
    print "***** Rules parsed *****"
    w.print_rules()
    w.test_times()


# Run "$ python timewriter.py en" to check all rules for English ("en" argument)
# Run "$ python timewriter.py en 1" to get profiling information.
if __name__ == "__main__":
    import sys
    if len(sys.argv) > 2:
        import cProfile
        cProfile.run("main()", "genprof")
        import pstats
        p = pstats.Stats("genprof")
        print
        print "***** Profiling *****"
        p.strip_dirs().sort_stats("time", "name").print_stats(0.1)
    else:
        main()

