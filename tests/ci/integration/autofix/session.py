import json
import shlex
from pathlib import Path
from typing import Self

from pydantic import BaseModel, Field, computed_field
from strands.agent import Agent
from strands.types.content import Messages
from strands.types.event_loop import Usage

# Bedrock prices for Claude Opus 5.5, in USD per million tokens.
_USD_PER_MTOK = {"inputTokens": 4.00, "outputTokens": 20.00, "cacheReadInputTokens": 0.20,
                 "cacheWriteInputTokens": 5.00}


class Session(BaseModel):
    """One agent run's token usage and price."""
    model: str
    usage: Usage
    transcript: str = Field(exclude=True)

    @classmethod
    def of(cls, agent: Agent, model: str) -> Self:
        return cls(
            model=model,
            usage=agent.event_loop_metrics.accumulated_usage,
            transcript=cls._markdown(agent.messages),
        )

    @computed_field
    @property
    def cost_usd(self) -> float:
        return sum(self.usage.get(field, 0) * rate for field, rate in _USD_PER_MTOK.items()) / 1_000_000

    def save(self, out: Path, name: str) -> None:
        (out / f"{name}-transcript.md").write_text(self.transcript)
        (out / f"{name}-session.json").write_text(self.model_dump_json(indent=2))

    @staticmethod
    def _markdown(messages: Messages) -> str:
        """Return the reasoning, text, and tool calls as markdown."""
        lines = []
        for message in messages:
            for block in message["content"]:
                match block:
                    case {"reasoningContent": {"reasoningText": {"text": text}}} | {"text": text}:
                        lines.append(f"{text}\n")
                    case {"toolUse": {"name": "run_command" as name, "input": {"argv": argv}}}:
                        lines.append(f"[tool] **{name}**\n```\n{shlex.join(argv)}\n```\n")
                    case {"toolUse": {"name": name, "input": tool_input}}:
                        arg = tool_input.get("path") or tool_input.get("name") or json.dumps(tool_input)
                        lines.append(f"[tool] **{name}**\n```\n{arg}\n```\n")
        return "\n".join(lines)
