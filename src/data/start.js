import * as icons from "../icons";
import IframeWindow from "../components/IframeWindow";
import Notepad from "../components/Notepad";
import JSDos from "../components/JSDos";

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
    data: { src: "https://jspaint.app/" },
    multiWindow: true
  }
];

const programs = [
  { title: "Accessories", icon: icons.folderProgram16, options: accessories },
  { title: "Online Services", icon: icons.folderProgram16, options: [] },
  { title: "StartUp", icon: icons.folderProgram16, options: [] },
  { title: "Internet Explorer", icon: icons.internetExplorere16 },
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
  { title: "Links", icon: icons.folder16, options: [] },
  { title: "Media", icon: icons.folder16, options: [] },
  { title: "MSN", icon: icons.htmlFile16, onClick: goTo("https://msn.com") },
  {
    title: "Radio Station Guide",
    icon: icons.htmlFile16,
    onClick: goTo("https://msn.com")
  },
  { title: "Web Events", icon: icons.htmlFile16, isDisabled: true }
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
