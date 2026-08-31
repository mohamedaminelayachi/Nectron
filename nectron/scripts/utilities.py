import os
import json

from typing import Union
from dataclasses import dataclass


@dataclass
class NectronState:
    program_description: Union[str, None]
    acsl_contracts: Union[str, None]
    seeds: Union[str, None]
    srs: Union[str, None]
    nar_representation: Union[str, None]
    suggestions: Union[list, None]

    def to_dict(self, unroll_suggestions: bool=False):
        if unroll_suggestions:
            data = {
                "program_description": self.program_description,
                "acsl_contracts": self.acsl_contracts,
                "sequential_reasoning_strategy": self.srs,
                "seeds": self.seeds,
                "nar_representation": self.nar_representation
            }

            for index, s in enumerate(self.suggestions):
                data[f'suggestion_{index+1}'] = s

            return data
        else:
            return {
                "program_description": self.program_description,
                "acsl_contracts": self.acsl_contracts,
                "sequential_reasoning_strategy": self.srs,
                "seeds": self.seeds,
                "nar_representation": self.nar_representation,
                "suggestions": self.suggestions
            }

    def is_empty(self):

        values = [item for item in self.to_dict(unroll_suggestions=True).values()]
        for value in values:
            if value is not None and len(value) > 0:
                return False

        return True

    def is_full(self):
        return not self.is_empty()

    def __matmul__(self, other):
        if self == other:
            return other
        if isinstance(other, NectronState):
            if len(self.program_description) == 0:
                self.program_description = other.program_description
            if len(self.acsl_contracts) == 0:
                self.acsl_contracts = other.acsl_contracts
            if len(self.srs) == 0:
                self.srs = other.srs
            if len(self.seeds) == 0:
                self.seeds = other.seeds
            if len(self.nar_representation) == 0:
                self.nar_representation = other.nar_representation

            self.suggestions = other.suggestions

        return self


def nullable_processor(item):
    if item is None:
        return ''
    else:
        return item


def read_nectron_file(file_path: str):
    if os.path.exists(file_path):
        with open(file_path, 'r') as fp:
            file = json.load(fp)

        state_entries = [
            "program_description",
            "acsl_contracts",
            "seeds",
            "sequential_reasoning_strategy",
            "nar_representation"
            "suggestions",
        ]

        for entry in file:
            if entry not in state_entries:
                return None

        state = NectronState(
            program_description=file['program_description'],
            acsl_contracts=file['acsl_contracts'],
            seeds=file['seeds'],
            srs=file['sequential_reasoning_strategy'],
            nar_representation=file['nar_representation'],
            suggestions=file['suggestions']
        )

        return state
    else:
        return None


def read_nectron_settings(file_path: str):
    if os.path.exists(file_path):
        with open(file_path, 'r') as fp:
            file = json.load(fp)

        config_entries = [
            'api_key',
            'backend_model',
            'model_identifier',
            'reflective_reasoning_intensity',
            'default_export_extension',
            'program_description',
            'acsl_contracts',
            'srs',
            'nar_representation',
            'seeds'
        ]

        configuration = {}
        for entry in file:
            configuration[entry] = file[entry]
            if entry not in config_entries:
                return None

        return configuration
    else:
        raise FileNotFoundError
