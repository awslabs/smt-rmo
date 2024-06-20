import secrets
import string
from abc import ABC, abstractmethod
from typing import Any


class Tokenizer(ABC):
    @abstractmethod
    def encode(self, value: Any) -> Any:
        raise NotImplementedError

    def decode(self, value: Any) -> Any:
        raise NotImplementedError


class CounterTokenizer(Tokenizer):
    def __init__(self, initial_value: int = 0):
        self._counter = 0

    def encode(self, value: Any) -> Any:
        self._counter += 1
        return self._counter


class RandomTokenizer(Tokenizer):
    DEFAULT_STRING_LENGHT: int = 10
    DEFAULT_NUMBER_LOWER_BOUND: float = -10e6
    DEFAULT_NUMBER_UPPER_BOUND: float = 1e6

    def __init__(self, seed: int = None):
        self._rng = secrets.SystemRandom()
        if seed is not None:
            self._rng.seed(seed)
        self._charset = string.ascii_letters + string.digits

    def encode(self, value: Any) -> Any:
        if isinstance(value, bool):
            return self.random_bool()
        if isinstance(value, str):
            return self.random_string()
        if isinstance(value, int):
            return self.random_int()
        if isinstance(value, float):
            return self.random_float()
        return super().encode(value)

    def random_identifier(self, length: int = DEFAULT_STRING_LENGHT) -> str:
        return "".join(self._rng.choice(string.ascii_letters) for _ in range(length))

    def random_string(self, length: int = DEFAULT_STRING_LENGHT) -> str:
        return "".join(self._rng.choice(self._charset) for _ in range(length))

    def random_int(
        self,
        lower_bound: float = DEFAULT_NUMBER_LOWER_BOUND,
        upper_bound: float = DEFAULT_NUMBER_UPPER_BOUND,
    ) -> int:
        return self._rng.randint(int(lower_bound), int(upper_bound))

    def random_float(
        self,
        lower_bound: float = DEFAULT_NUMBER_LOWER_BOUND,
        upper_bound: float = DEFAULT_NUMBER_UPPER_BOUND,
    ) -> float:
        return self._rng.uniform(float(lower_bound), float(upper_bound))

    def random_bool(self) -> bool:
        return self._rng.choice([True, False])

    def random_bv(self, width: int) -> str:
        return "".join(self._rng.choice(["0", "1"]) for _ in range(width))

    # returns a hexadecimal representation of random character, using #x... format
    def random_hex_character(self) -> str:
        return hex(ord(self._rng.choice(self._charset))).replace("0x", "#x")
