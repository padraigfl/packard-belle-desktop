import * as icons from "../icons";
import ExplorerWindow from "../components/ExplorerWindow";
import IframeWindow from "../components/IframeWindow";

export default [
  {
    title: "My Computer",
    icon: icons.computer32,
    Component: ExplorerWindow,
    data: {
      content: "Lets not go crazy here, don't write an OS in JS..."
    },
    onClick: () => {}
  },
  {
    title: "Paint",
    icon: icons.paint16,
    Component: IframeWindow,
    data: { src: "https://jspaint.app/" }
  }
];
