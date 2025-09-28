

class UnspecifiedNARSourceFile(Exception):
    """The NAR source file is not valid or not provided. Make sure your provide a valid NAR source file."""

    def __str__(self):
        return ("The NAR source file is not valid or not provided."
                " Make sure you provide a valid source file.")


class UnspecifiedNARGrammarFile(Exception):
    """The NAR grammar file is not valid or not provided. Make sure your provide a valid NAR grammar file."""

    def __str__(self):
        return ("The NAR grammar file is not valid or not provided."
                " Make sure you provide a valid grammar file.")


class NonCompilableNAR(Exception):
    """The NAR program is not compilable. Make sure you provide correct NAR syntax."""

    def __str__(self):
        return ("The NAR program is not compilable."
                " Make sure you provide correct NAR syntax.")
