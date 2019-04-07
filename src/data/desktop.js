import * as icons from "../icons";
import ExplorerWindow from "../components/ExplorerWindow";
import IframeWindow from "../components/IframeWindow";
import Notepad from "../components/Notepad";
import facepalm from "./textFiles/facepalm";

export default [
  {
    title: "My Computer",
    icon: icons.computer32,
    Component: ExplorerWindow,
    data: {
      content: "Lets not go crazy here, don't write an OS in JS..."
    }
  },
  {
    title: "Component Library that I made for this thing",
    icon: icons.internetExplorere32,
    onClick: () => window.open("https://github.com/padraigfl/packard-belle")
  },
  {
    title: "Paint",
    icon: icons.paint32,
    Component: IframeWindow,
    data: { src: "https://jspaint.app/" }
  },
  {
    title: "facepalm",
    icon: icons.notepadFile32,
    Component: Notepad,
    data: {
      content: facepalm
    }
  }
];
