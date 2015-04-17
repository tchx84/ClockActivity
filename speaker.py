#! /usr/bin/env python
# -*- coding: utf-8 -*-
#
# Code released in the Public Domain. You can do whatever you want with this package.
# Look at NOTES file to see how to adapt this program.
# Originally written by Pierre Métras <pierre@alterna.tv> for the OLPC XO laptop.


"""
Speak aloud the text given in the XO configured language.

Controls the espeak program available on the OLPC XO laptop.
"""

import sys
import os

from gettext import gettext as _


class Speaker:
    """Speak aloud the given text.
    """

    """espeak parameter: language pitch.
    """
    # TRANS: The language pitch (range [0 - 99], default 50 for English)
    # Look at http://espeak.sourceforge.net/commands.html for details
    PITCH = _("50")


    """espeak parameter: diction speed (average words per minute).
    """
    # TRANS: The diction speed, in average words per minute (range [80 - 390],
    # default 170 for English).
    # Look at http://espeak.sourceforge.net/commands.html for details
    SPEED = _("170")


    """espeak parameter: word gap in units of 10 ms.
    """
    # TRANS: The pause duration between words, in units of 10 ms.
    # Look at http://espeak.sourceforge.net/commands.html for details
    WORD_GAP = _("0")


    """espeak parameter: the language and voice variant.
    """
    # TRANS: The language and voice variant
    # Look at http://espeak.sourceforge.net/commands.html for details, and
    # http://espeak.sourceforge.net/languages.html to see if your language is supported.
    VOICE = _("en")

    ESPEAK_COMMAND = "espeak -p%s -s%s -g%s -v%s \"%s\""

    def speak(self, text):
        """Speaks aloud the given text.
        """
        text = text.replace("\"", "\\\"")
        child = os.popen(Speaker.ESPEAK_COMMAND %
                        (Speaker.PITCH,
                         Speaker.SPEED,
                         Speaker.WORD_GAP,
                         Speaker.VOICE,
                         text))
        child.read()
        child.close()


if __name__ == "__main__":
    s = Speaker()
    s.speak("It's two o'clock in the morning")
    s.speak("It's seven hours and thirty-four minutes PM")
    #s.speak("Il est quinze heures et vingt-neuf minutes")
    #s.speak("vingt-deux heures dix-huit minutes")

