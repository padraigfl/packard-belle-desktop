import React from "react";
import cx from "classnames";
import * as icons from "../../icons";
import "./_styles.scss";
import { WindowExplorer } from "packard-belle";
import Window from "../tools/Window";

const noop = () => {};

export const buildMenu = props => [
  {
    title: "File",
    options: [
      { title: "Open", isDisabled: true },
      { title: "Close", onClick: () => props.onClose(props.id) }
    ]
  },
  {
    title: "Help",
    options: [{ title: `About ${props.title}`, isDisabled: true }]
  }
];

const InternetExplorer = props => (
  <Window
    {...props}
    Component={WindowExplorer}
    className={cx("Internet Explorer", props.className)}
    title={`${
      props.data.title || props.title !== "Internet Explorer"
        ? `${props.data.title || props.title} - `
        : ""
    }Internet Explorer`}
    menuOptions={buildMenu(props)}
    explorerOptions={[
      {
        icon: icons.back,
        title: "Back",
        onClick: noop
      },
      {
        icon: icons.forward,
        title: "Forward",
        onClick: noop
      },
      {
        icon: icons.ieStop,
        title: "Stop",
        onClick: noop
      },
      {
        icon: icons.ieRefresh,
        title: "Refresh",
        onClick: noop
      },
      {
        icon: icons.ieHome,
        title: "Home",
        onClick: noop
      },
      [
        {
          icon: icons.ieSearch,
          title: "Search",
          onClick: noop
        },
        {
          icon: icons.ieFavorites,
          title: "Favorites",
          onClick: noop
        },
        {
          icon: icons.ieHistory,
          title: "History",
          onClick: noop
        }
      ],
      {
        icon: icons.ieMail,
        title: "Mail",
        onClick: noop
      },
      {
        icon: icons.iePrint,
        title: "Print",
        onClick: noop
      }
    ]}
    maximizeOnOpen
  >
    {props.data.html && <div dangerouslySetInnerHTML={props.data.html} />}
    {props.children}
    {props.data && props.data.src && (
      <iframe
        scrolling="no"
        frameBorder="0"
        src={props.data.src}
        title={props.data.src}
        importance="low"
      />
    )}
  </Window>
);

export default InternetExplorer;

// initialHeight, initialWidth, title, icon, footer, id,
// onClose, onMaximize, isActive, explorerOptions, chidlren, data, customSelect, Component
