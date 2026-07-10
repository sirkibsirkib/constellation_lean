import Constellation

def hello := "World"

-- dummy entrypoint
def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
