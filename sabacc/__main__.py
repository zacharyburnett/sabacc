from textual.app import App, ComposeResult
from textual.widgets import Header, Footer


class Sabacc(App):
    def compose(self) -> ComposeResult:
        yield Header()
        yield Footer()


def main():
    sabacc = Sabacc()
    sabacc.run()
    
if __name__ == '__main__':
    main()
