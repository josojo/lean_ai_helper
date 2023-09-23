class Mwe:
    ### Mwe class that defines the code which should be parsed or interacted with.
    ### Mwe stands for https://leanprover-community.github.io/mwe.html
    code: str
    name: str
    interaction_start: int
    interaction_end: int

    def __init__(
        self, code: str, name: str, interaction_start: int, interaction_end: int
    ):
        self.code = code
        self.name = name
        self.interaction_start = interaction_start
        self.interaction_end = interaction_end
