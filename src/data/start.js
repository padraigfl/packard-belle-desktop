import * as icons from "../icons";

const startMenu = [
  [
    {
      title: "Windows Update",
      icon: icons.windowsUpdate24,
      onClick: () => {
        window.location = "www.google.com";
      }
    }
  ],
  [
    {
      title: "Programs",
      icon: icons.programs24,
      options: []
    },
    {
      title: "Favorites",
      icon: icons.favorites24,
      options: []
    },
    {
      title: "Documents",
      icon: icons.documents24,
      options: []
    },
    {
      title: "Settings",
      icon: icons.settings24,
      options: []
    },
    {
      title: "Find",
      icon: icons.find24,
      options: []
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
  [
    {
      title: "Log Off",
      icon: icons.logOff24
    },
    {
      title: "Shut Down...",
      icon: icons.shutDown24
    }
  ]
];

export default startMenu;
