import * as icons from "../icons";
import ExplorerWindow from "../components/ExplorerWindow";

const goTo = url => () => window.open(url);

const accessories = [
  { title: "Entertainment", icon: icons.folderProgram16, options: [] },
  { title: "Internet Tools", icon: icons.folderProgram16, options: [] },
  { title: "System Tools", icon: icons.folderProgram16, options: [] },
  { title: "Calculator", icon: icons.calculator16 },
  { title: "Notepad", icon: icons.notepad16 },
  { title: "Paint", icon: icons.paint16 }
];

const programs = [
  { title: "Accessories", icon: icons.folderProgram16, options: accessories },
  { title: "Online Services", icon: icons.folderProgram16, options: [] },
  { title: "StartUp", icon: icons.folderProgram16, options: [] },
  { title: "Internet Explorer", icon: icons.internetExplorere16 },
  { title: "MS-DOS Prompt", icon: icons.msDos16 },
  { title: "Outlook Express", icon: icons.outlook16 },
  { title: "Windows Explorer", icon: icons.windowsExplorer16 }
];

const favorites = [
  {
    title: "Channels",
    options: [],
    icon: icons.folder16
  },
  { title: "Links", icon: icons.folder16, options: [] },
  { title: "Media", icon: icons.folder16, options: [] },
  { title: "MSN", icon: icons.htmlFile16, onClick: goTo("www.msn.com") },
  {
    title: "Radio Station Guide",
    icon: icons.htmlFile16,
    onClick: goTo("www.msn.com")
  },
  { title: "Web Events", icon: icons.htmlFile16, onClick: goTo("www.msn.com") }
];

const find = [
  { title: "Files or Folders...", icon: icons.findFiles16, onClick: goTo("") },
  {
    title: "Comuter...",
    icon: icons.findComputer16,
    onClick: goTo("")
  },
  { title: "On the Internet...", icon: icons.findOnline16, onClick: goTo("") },
  {
    title: "People...",
    icon: icons.findPeople16,
    onClick: goTo("")
  }
];

const settings = [
  [
    { title: "Control Panel", icon: icons.controlPanel16, onClick: goTo("") },
    {
      title: "Printers",
      icon: icons.controlPanel16,
      component: ExplorerWindow,
      data: {},
      onClick: () => {}
    },
    {
      title: "Taskbar & Start Menu...",
      icon: icons.settingsTaskbar16,
      component: ExplorerWindow,
      onClick: () => {}
    },
    {
      title: "Folder Options",
      icon: icons.folderOptions16,
      onClick: goTo("")
    },
    {
      title: "Active Desktop",
      icon: icons.activeDesktop16,
      onClick: goTo("")
    }
  ],
  {
    title: "Windows Update...",
    icon: icons.windowsUpdate16,
    onClick: goTo("")
  }
];

const startMenu = [
  {
    title: "Windows Update",
    icon: icons.windowsUpdate24,
    onClick: () => {
      window.location = "www.google.com";
    }
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
    icon: icons.logOff24
  },
  {
    title: "Shut Down...",
    icon: icons.shutDown24
  }
];

export default startMenu;
