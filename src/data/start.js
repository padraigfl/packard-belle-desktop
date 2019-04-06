import * as icons from "../icons";
import ExplorerWindow from "../components/ExplorerWindow";
import IframeWindow from "../components/IframeWindow";
import Notepad from "../components/Notepad";

const goTo = url => () => window.open(url);

const accessories = [
  { title: "Entertainment", icon: icons.folderProgram16, options: [] },
  { title: "Internet Tools", icon: icons.folderProgram16, options: [] },
  { title: "System Tools", icon: icons.folderProgram16, options: [] },
  { title: "Calculator", icon: icons.calculator16, isDisabled: true },
  { title: "Notepad", icon: icons.notepad16, Component: Notepad },
  {
    title: "Paint",
    icon: icons.paint16,
    Component: IframeWindow,
    data: { src: "https://jspaint.app/" }
  }
];

const programs = [
  { title: "Accessories", icon: icons.folderProgram16, options: accessories },
  { title: "Online Services", icon: icons.folderProgram16, options: [] },
  { title: "StartUp", icon: icons.folderProgram16, options: [] },
  { title: "Internet Explorer", icon: icons.internetExplorere16 },
  { title: "JS-DOS Prompt", icon: icons.msDos16, isDisabled: true },
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

const find = [
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

const settings = [
  [
    {
      title: "Control Panel",
      icon: icons.controlPanel16,
      Component: ExplorerWindow,
      data: {
        content: "Control panel stuff here"
      },
      onClick: () => {}
    },
    // {
    //   title: "Printers",
    //   icon: icons.controlPanel16,
    //   Component: ExplorerWindow,
    //   isDisabled: true
    // },
    {
      title: "Taskbar & Start Menu...",
      icon: icons.settingsTaskbar16,
      Component: ExplorerWindow,
      onClick: () => {}
    }
    // {
    //   title: "Folder Options",
    //   icon: icons.folderOptions16,
    //   isDisabled: true
    // },
    // {
    //   title: "Active Desktop",
    //   icon: icons.activeDesktop16,
    //    // minimize all
    // }
  ],
  {
    title: "Windows Update...",
    icon: icons.windowsUpdate16
  }
];

const startMenu = [
  {
    title: "Windows Update",
    icon: icons.windowsUpdate24,
    isDisabled: true
    // onClick: () => {
    //   window.location = "https://google.com";
    // }
  },
  [
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
    },
    {
      title: "Settings",
      icon: icons.settings24,
      options: settings
    },
    {
      title: "Find",
      icon: icons.find24,
      options: find
    },
    {
      title: "Help",
      icon: icons.help24,
      options: []
    },
    {
      title: "Run...",
      icon: icons.run24,
      options: []
    }
  ],
  {
    title: "Log Off",
    icon: icons.logOff24,
    isDisabled: true
  },
  {
    title: "Shut Down...",
    icon: icons.shutDown24
  }
];

export default startMenu;
