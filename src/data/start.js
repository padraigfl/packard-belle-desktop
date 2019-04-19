import * as icons from "../icons";
import IframeWindow from "../components/IframeWindow";
import Notepad from "../components/Notepad";
import JSDos from "../components/JSDos";
import InternetExplorer from "../components/InternetExplorer/InternetExplorer";
import google1999 from "./textFiles/google1999";

const goTo = url => () => window.open(url);

const accessories = [
  { title: "Entertainment", icon: icons.folderProgram16, options: [] },
  { title: "Internet Tools", icon: icons.folderProgram16, options: [] },
  { title: "System Tools", icon: icons.folderProgram16, options: [] },
  { title: "Calculator", icon: icons.calculator16, isDisabled: true },
  {
    title: "Notepad",
    icon: icons.notepad16,
    Component: Notepad,
    multiWindow: true
  },
  {
    title: "Paint",
    icon: icons.paint16,
    Component: IframeWindow,
    data: { src: "https://jspaint.app/", creator: "https://github.com/1j01" },
    multiWindow: true
  },
  {
    title: "SkiFree",
    icon: icons.skifree,
    Component: IframeWindow,
    data: {
      src: "https://basicallydan.github.io/skifree.js/"
    },
    multiWindow: true
  },
  {
    title: "Minesweeper",
    icon: icons.minesweeper16,
    Component: IframeWindow,
    data: {
      src: "https://mines.now.sh/",
      creator: "https://github.com/ShizukuIchi",
      height: 225,
      width: 150,
      style: {
        transform: "scale(0.5) translateX(-50%) translateY(-50%)",
        width: "300px",
        height: "400px"
      }
    },
    multiWindow: true
  }
];

const programs = [
  { title: "Accessories", icon: icons.folderProgram16, options: accessories },
  { title: "Online Services", icon: icons.folderProgram16, options: [] },
  { title: "StartUp", icon: icons.folderProgram16, options: [] },
  {
    title: "IE4(BROKEN)",
    icon: icons.internetExplorere16,
    Component: InternetExplorer,
    data: { __html: google1999 }
  },
  {
    title: "JS-DOS Prompt",
    icon: icons.msDos16,
    Component: JSDos,
    multiWindow: true
  },
  { title: "Outlook Express", icon: icons.outlook16, isDisabled: true },
  { title: "Windows Explorer", icon: icons.windowsExplorer16, isDisabled: true }
];

const favorites = [
  {
    title: "Channels",
    options: [],
    icon: icons.folder16
  },
  {
    title: "Links",
    icon: icons.folder16,
    options: [
      {
        title: "MySpace",
        type: "ExternalLink",
        icon: icons.htmlFile16,
        onClick: () => {
          if (window.confirm("This will open a new tab, is that okay?")) {
            window.open(
              "https://web.archive.org/web/20080320075546/www.myspace.com/my_address"
            );
          }
        }
      }
    ]
  },
  {
    title: "Media",
    icon: icons.folder16,
    options: [
      {
        title: "My Big List of Films",
        type: "ExternalLink",
        icon: icons.htmlFile16,
        onClick: () => {
          if (window.confirm("This will open a new tab, is that okay?")) {
            window.open("https://letterboxd.com/padraig");
          }
        }
      }
    ]
  },
  {
    title: "My Github",
    type: "ExternalLink",
    icon: icons.htmlFile16,
    onClick: () => {
      if (window.confirm("This will open a new tab, is that okay?")) {
        window.open("https://github.com/padraigfl");
      }
    }
  }
];

export const find = [
  { title: "Files or Folders...", icon: icons.findFiles16, isDisabled: true },
  {
    title: "Computer...",
    icon: icons.findComputer16,
    isDisabled: true
  },
  {
    title: "On the Internet...",
    icon: icons.findOnline16,
    onClick: goTo("https://google.com")
  },
  {
    title: "People...",
    icon: icons.findPeople16,
    onClick: goTo("https://facebook.com")
  }
];

export default [
  {
    title: "Programs",
    icon: icons.folderProgram24,
    options: programs
  },
  {
    title: "Favorites",
    icon: icons.folderFavorites24,
    options: favorites
  },
  {
    title: "Documents",
    icon: icons.folderOpen24,
    options: []
  }
];
